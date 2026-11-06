From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_main_inv
  codec_main_rdb_lib diginet_ring_encode_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The frame after the store of a (the word wA), b still 0. *)
Definition rd5_cells (pv dv : Z) (wA inp inn : word) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0); C4 (Z_to_bv 64 5); CB 4 (fz0 4); C8 (Z_to_bv 64 pv);
   C8 (Z_to_bv 64 dv); C4 wA; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 32 (fa5 32); CB 32 (fa5 32); C4 (Z_to_bv 64 0); CB 24 (fz0 24);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 inp; C8 inn; CB 80 tl].

(** 0x14194-0x141b0: b = the u16 composed and stored, diginet_ring_encode(k.p, a, (u16) b, &k.out), j JOIN. *)
Lemma rd5_tail : diginet_ring_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd5_cells pv dv wA inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem ->
    bv_unsigned a0w < 2 ^ 16 -> bv_unsigned a1w < 2 ^ 16 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x14194 m1).
Proof.
  intros CR e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA inp inn
         pv dv od c rem tl m1 FR HFR HF HPD HC -> -> Ha0 Ha1.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0w) as Ra0. unfold bv_modulus in Ra0.
  pose proof (bv_unsigned_in_range 64 a1w) as Ra1. unfold bv_modulus in Ra1.
  pose proof HE as (_ & _ & _ & HLO & _).
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  unfold rd5_cells in FR.
  zstep.
  assert (HL : 0 <= Z.lor (bv_unsigned a1w) (bv_unsigned a0w) < 2 ^ 16) by (apply lor_lt_pow2; lia).
  remember (Z_to_bv 64 (Z.lor (bv_unsigned a1w) (bv_unsigned a0w))) as Wb eqn:EWb.
  assert (HWb : bv_unsigned Wb < 2 ^ 16) by (rewrite EWb; rewrite unsigned_lit by lia; lia).
  clear EWb HL.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HR : ov_read_bytes rsegs mm (wa (bv_unsigned (e_sp e) + -400 + 44)) 2 = Some (le2 Wb)) end.
  { pose proof FR as [[Hwf HBY] _].
    rewrite (bytes_at_read rsegs _ _ _ 44 2 HBY) by (try lia; rewrite cells_bytes_length by exact Hwf; cbn; lia).
    reflexivity. }
  zstep. zstep. clear HR.
  zstep. zstep. zstep.
  destruct (rw_cells_cut3 _ _ _ 14%nat (CB 32 (fa5 32)) FR eq_refl) as (PRE & OUT & POST). clear FR.
  norm_piece PRE. norm_piece OUT. norm_piece POST.
  replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) in OUT, POST by lia.
  assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  set (strip := bv_unsigned wA mod 2 ^ 32).
  assert (Hstrip : 0 <= strip < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  set (mask := bv_unsigned Wb mod 2 ^ 16).
  assert (Hmask : 0 <= mask < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
  unfold diginet_ring_encode_contract, DIGINET_RING_ENCODE, DIGINET_RING_ENCODE_DEPTH in CR.
  call (CR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e_lo e) od strip mask (fa5 32)).
  { unfold diginet_ring_encode_pre, DIGINET_RING_ENCODE_DEPTH. rewrite U276, USP.
    split; [ apply (pers_arg_of_pd _ pv dv od); [ exact (relro_of_munch e _ HE MU) | exact HPD ] | ].
    split; [ split; [exact Hstrip | apply sx32_s32] | ].
    split; [ split; [exact Hmask | reflexivity] | ].
    split; [lia|]. split; [exact OUT|]. split; [lia|]. split; [exact HMI|]. split; [exact ST | lia]. }
  rewrite ?USP, ?U276 in *.
  match goal with H : context [ring_spec od strip mask] |- _ =>
    rewrite (surjective_pairing (ring_spec od strip mask)) in H; cbv beta iota in H; destruct H as [Ea0 OUT2] end.
  rewrite Ea0.
  zstep.
  apply (rw_cells_C4 _ _ _ 40%nat wA strip) in PRE; [ | reflexivity | apply Z.mod_mod; lia ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  apply (rw_cells_C4 _ _ _ 44%nat Wb (bv_unsigned Wb)) in PRE; [ | reflexivity | reflexivity ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  pose proof (rw_cells_join3 _ _ _ _ _ _ _ PRE OUT2 POST) as FJ.
  specialize (FJ ltac:(norm_sizes; lia) ltac:(norm_sizes; lia)).
  set (k := mkKcall 5 (fz0 4) pv dv strip (bv_unsigned Wb) 0 0 (fz0 24) 0 0 (fa5 32)
                    (cmd_out (fa5 32) (snd (ring_spec od strip mask))) 0 (fz0 24) 0 0 0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FB : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FJ end.
  clear FJ PRE OUT2 POST.
  assert (EK : fst (ring_spec od strip mask) = fst (enc_k k od)) by reflexivity.
  rewrite EK.
  unfold join_ok, st, body_regs in JN.
  eapply JN; [ exact HF | | exact HC | exact FB | unfold fr_ok; repeat (split; [eassumption|]); eassumption ].
  unfold rec_ok. split; [unfold k; cbn; lia|]. split; [exact HPD|]. split.
  { unfold rdr_k, k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
    pose proof (bv_unsigned_in_range 64 Wb) as RWb. unfold bv_modulus in RWb.
    apply rdr_fz0; try lia; try (intros; discriminate). }
  split; reflexivity.
Qed.

Ltac rd_close Hcur :=
  first [ reflexivity | (unfold cur_ok; lia) | (rewrite Hcur; f_equal; lia) | (f_equal; lia)
        | (rewrite <- Hcur; symmetry; apply Z_to_bv_bv_unsigned) ].

(** The u16 bound of a byte register (lbu) or of a byte shifted by 8 (slli). *)
Ltac b16 :=
  first [ (rewrite unsigned_lit by lia; lia)
        | (rewrite Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by lia; lia)
        | (rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia; rewrite unsigned_lit by lia; lia) ].

(** 0x1414c-0x14190: b = fuzz_u16 (two fuzz_u8, a missing byte reads 0); a1 = the bytes left. *)
Lemma rd5_b : diginet_ring_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd5_cells pv dv wA inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem -> a1w = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x1414c m1).
Proof.
  intros CR e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wA inp inn
         pv dv od c rem tl m1 FR HFR HF HPD HC -> -> ->.
  pose proof (rd5_tail CR e fuel HE JN) as TL. unfold st, body_regs in TL.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  unfold rd5_cells in FR.
  set (cur := Z_to_bv 64 (bv_unsigned (e_p e) + c)) in FR.
  assert (Hcur : bv_unsigned cur = bv_unsigned (e_p e) + c) by (unfold cur; apply unsigned_lit; lia).
  clearbody cur.
  zstep.
  if_cases E0.
  { zify_cond E0. do 2 zstep.
    eapply TL with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      first [ rd_close Hcur | b16 ]. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 1 zstep.
    eapply TL with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      first [ rd_close Hcur | b16 ]. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  eapply TL with (od := od) (c := c + 2) (rem := rem - 2);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    first [ rd_close Hcur | b16 ].
Qed.

(** 0x14138-0x14148: a composed and stored; then the u16. *)
Lemma rd5_a : diginet_ring_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4w a5' a6' a7' s8' s10' t3' t4' t5' t6' ops inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd_cells 5 pv dv inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem -> a1w = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4w a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x14138 m1).
Proof.
  intros CR e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4w a5' a6' a7' s8' s10' t3' t4' t5' t6' ops inp inn
         pv dv od c rem tl m1 FR HFR HF HPD HC Einp Einn Ea1.
  pose proof (rd5_b CR e fuel HE JN) as TB. unfold st, body_regs in TB.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  unfold rd_cells in FR. cbn [kcall_cells k_rd k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc
    k_before k_out k_want_rc k_want k_want_len k_want_key k_want_display app] in FR.
  do 5 zstep.
  eapply TB with (od := od) (c := c) (rem := rem);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | exact HC
    | exact Einp | exact Einn | exact Ea1 ].
Qed.

(** 0x137bc-0x1382c, 0x13ad0-0x13ad8, 0x13b78-0x13b7c, 0x1412c-0x14134: a = fuzz_u32 (four fuzz_u8, a
    missing byte reads 0), in.p / in.n advanced by the bytes taken, a1 = the bytes left; then a's store. *)
Lemma codec_main_rd5 : S_rd5.
Proof.
  unfold S_rd5. intros CR e fuel HE JN.
  pose proof (rd5_a CR e fuel HE JN) as TL. unfold st, body_regs in TL.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  replace (rd_pc 5) with 0x137bc by (vm_compute; reflexivity).
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
  { zify_cond E0. do 5 zstep.
    eapply TL with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 3 zstep.
    eapply TL with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  if_cases E2.
  { zify_cond E2. do 3 zstep.
    eapply TL with (od := od) (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte cur c 2. zstep. zstep.
  if_cases E3.
  { zify_cond E3. do 3 zstep.
    eapply TL with (od := od) (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte cur c 3. zstep. zstep. zstep.
  eapply TL with (od := od) (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd_close Hcur.
Qed.
