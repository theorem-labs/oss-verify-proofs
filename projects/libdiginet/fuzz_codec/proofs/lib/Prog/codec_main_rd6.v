From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_main_inv
  codec_main_rdb_lib diginet_meter_encode_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The frame inside the METER reader: k as HEAD leaves it with the words wa, wb, wc in the fields a, b, c,
    in.p / in.n the words inp / inn. *)
Definition rd6_cells (pv dv : Z) (wa wb wc inp inn : word) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
   C4 (Z_to_bv 64 6); CB 4 (fz0 4); C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 dv);
   C4 wa; C4 wb; C4 wc; C4 (Z_to_bv 64 0);
   CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   CB 32 (fa5 32); CB 32 (fa5 32);
   C4 (Z_to_bv 64 0); CB 24 (fz0 24); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 inp; C8 inn; CB 80 tl].

Lemma s32_range6 : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= s32 v < 2 ^ 31.
Proof. intros v Hv. unfold s32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.

Ltac rd6_close Hcur :=
  first [ reflexivity | (unfold cur_ok; lia) | (rewrite Hcur; f_equal; lia) | (f_equal; lia)
        | (rewrite <- Hcur; symmetry; apply Z_to_bv_bv_unsigned) ].

(** 0x14300-0x1432c: b composed and stored, a, b, c reloaded (lw),
    diginet_meter_encode(k.p, a, (int) c, b, &k.out), j JOIN. *)
Lemma rd6_call : diginet_meter_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd6_cells pv dv wa wb wc inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x14300 m1).
Proof.
  intros CM e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc
         inp inn pv dv od c rem tl m1 FR HFR HF HPD HC -> ->.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  destruct HFR as (SV & ST & MU & WM & HMI).
  pose proof ST as [Hlo0 _].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  unfold rd6_cells in FR.
  unfold LLVM_CODEC_STACK in *.
  do 5 zstep.
  lazymatch type of FR with context [C4 wa :: C4 ?X :: C4 wc :: _] =>
    remember X as W eqn:EW end.
  clear EW.
  do 6 zstep.
  destruct (rw_cells_cut3 _ _ _ 14%nat (CB 32 (fa5 32)) FR eq_refl) as (PRE & OUT & POST). clear FR.
  norm_piece PRE. norm_piece OUT. norm_piece POST.
  replace (bv_unsigned (e_sp e) + -400 + 124) with (bv_unsigned (e_sp e) + -276) in OUT, POST by lia.
  assert (U276 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -276)) = bv_unsigned (e_sp e) + -276)
    by (apply unsigned_lit; lia).
  set (va := bv_unsigned wa mod 2 ^ 32).
  set (vb := bv_unsigned W mod 2 ^ 32).
  set (vc := bv_unsigned wc mod 2 ^ 32).
  assert (Rva : 0 <= va < 2 ^ 32) by (unfold va; apply Z.mod_pos_bound; lia).
  assert (Rvb : 0 <= vb < 2 ^ 32) by (unfold vb; apply Z.mod_pos_bound; lia).
  assert (Rvc : 0 <= vc < 2 ^ 32) by (unfold vc; apply Z.mod_pos_bound; lia).
  unfold diginet_meter_encode_contract, DIGINET_METER_ENCODE, DIGINET_METER_ENCODE_DEPTH in CM.
  call (CM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e_lo e) od va (s32 vc) vb (fa5 32)).
  { unfold diginet_meter_encode_pre, DIGINET_METER_ENCODE_DEPTH. rewrite ?USP, ?U276.
    split; [ exact (pers_arg_of_pd _ pv dv od (relro_of_munch e _ HE MU) HPD) | ].
    split; [ split; [ exact Rva | exact (sx32_s32 wa) ] | ].
    split; [ split; [ exact (s32_range6 _ Rvc) | exact (sx32_s32 wc) ] | ].
    split; [ split; [ exact Rvb | exact (sx32_s32 W) ] | ].
    split; [ lia | ].
    split; [ exact OUT | ].
    split; [ lia | ].
    split; [ exact HMI | ].
    split; [ exact ST | lia ]. }
  rewrite ?USP, ?U276 in *.
  match goal with H : context [meter_spec od va (s32 vc) vb] |- _ =>
    rewrite (surjective_pairing (meter_spec od va (s32 vc) vb)) in H; cbv beta iota in H;
    destruct H as [Ea0 OUT2] end.
  rewrite Ea0.
  zstep.
  apply (rw_cells_C4 _ _ _ 40%nat wa va) in PRE; [ | reflexivity | unfold va; apply Z.mod_mod; lia ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  apply (rw_cells_C4 _ _ _ 44%nat W vb) in PRE; [ | reflexivity | unfold vb; apply Z.mod_mod; lia ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  apply (rw_cells_C4 _ _ _ 48%nat wc vc) in PRE; [ | reflexivity | unfold vc; apply Z.mod_mod; lia ].
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in PRE.
  pose proof (rw_cells_join3 _ _ _ _ _ _ _ PRE OUT2 POST) as FJ.
  specialize (FJ ltac:(norm_sizes; lia) ltac:(norm_sizes; lia)).
  set (k := mkKcall 6 (fz0 4) pv dv va vb vc 0 (fz0 24) 0 0 (fa5 32)
                    (cmd_out (fa5 32) (snd (meter_spec od va (s32 vc) vb))) 0 (fz0 24) 0 0 0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FB : rw_cells rsegs mm (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FJ end.
  clear FJ PRE OUT2 POST.
  assert (EK : fst (meter_spec od va (s32 vc) vb) = fst (enc_k k od)) by reflexivity.
  rewrite EK.
  unfold join_ok, st, body_regs in JN.
  eapply JN; [ exact HF | | exact HC | exact FB | ].
  - unfold rec_ok. split; [unfold k; cbn; lia|]. split; [exact HPD|]. split.
    { unfold rdr_k, k. cbn [k_kind k_a k_b k_c k_delta k_bytes k_n].
      apply rdr_fz0; try lia; try (intros; discriminate). }
    split; reflexivity.
  - unfold fr_ok. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(** 0x14278-0x142fc: b = fuzz_u32 (four fuzz_u8, a missing byte reads 0; a0 = in.n), then the call. *)
Lemma rd6_b : diginet_meter_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd6_cells pv dv wa wb wc inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem -> a0w = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x14278 m1).
Proof.
  intros CM e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc
         inp inn pv dv od c rem tl m1 FR HFR HF HPD HC Einp -> ->.
  pose proof (rd6_call CM e fuel HE JN) as TL. unfold st, body_regs in TL.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  unfold rd6_cells in FR.
  assert (Hcur : bv_unsigned inp = bv_unsigned (e_p e) + c) by (rewrite Einp; apply unsigned_lit; lia).
  clear Einp.
  zstep.
  if_cases E0.
  { zify_cond E0. do 4 zstep.
    eapply TL with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 inp c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 2 zstep.
    eapply TL with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte inp c 1. zstep. zstep. zstep.
  if_cases E2.
  { zify_cond E2. do 1 zstep.
    eapply TL with (od := od) (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte inp c 2. zstep. zstep.
  if_cases E3.
  { zify_cond E3. do 1 zstep.
    eapply TL with (od := od) (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte inp c 3. zstep. zstep. zstep.
  eapply TL with (od := od) (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd6_close Hcur.
Qed.

(** 0x141d4-0x14274: c = fuzz_u32 (a0 = in.n), stored at 0x14274; then block B. *)
Lemma rd6_c : diginet_meter_encode_contract -> forall e fuel, env_ok e -> join_ok e fuel ->
  forall (ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc inp inn : word)
         (pv dv : Z) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (rd6_cells pv dv wa wb wc inp inn tl) ->
    fr_ok e m1 ->
    fuel_ok ops (S fuel) -> pd_ok pv dv od -> cur_ok e c rem ->
    inp = Z_to_bv 64 (bv_unsigned (e_p e) + c) -> inn = Z_to_bv 64 rem -> a0w = Z_to_bv 64 rem ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
          0x141d4 m1).
Proof.
  intros CM e fuel HE JN ra' t0' t1' t2' a0w a1w a2w a3w a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops wa wb wc
         inp inn pv dv od c rem tl m1 FR HFR HF HPD HC Einp -> ->.
  pose proof (rd6_b CM e fuel HE JN) as TB. unfold st, body_regs in TB.
  unfold st, body_regs.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof HE as (_ & _ & _ & HLO & _ & DJ & HPB & _).
  pose proof (data_of_fr e m1 HE HFR) as HD.
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in *.
  pose proof ST as [Hlo0 _].
  pose proof HC as (Hc0 & Hr0 & Hcr).
  unfold rd6_cells in FR.
  assert (Hcur : bv_unsigned inp = bv_unsigned (e_p e) + c) by (rewrite Einp; apply unsigned_lit; lia).
  clear Einp.
  zstep.
  if_cases E0.
  { zify_cond E0. do 10 zstep.
    eapply TB with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 inp c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 8 zstep.
    eapply TB with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte inp c 1. zstep. zstep. zstep.
  if_cases E2.
  { zify_cond E2. do 8 zstep.
    eapply TB with (od := od) (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte inp c 2. zstep. zstep.
  if_cases E3.
  { zify_cond E3. do 8 zstep.
    eapply TB with (od := od) (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte inp c 3. do 8 zstep.
  eapply TB with (od := od) (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd6_close Hcur.
Qed.

(** 0x1389c-0x1390c, 0x13adc-0x13ae4, 0x13b80-0x13b84, 0x141b4-0x141d0: a = fuzz_u32, in.p / in.n advanced by
    the bytes taken (a0 = in.n), a stored at 0x141d0; then block C. *)
Lemma codec_main_rd6 : S_rd6.
Proof.
  unfold S_rd6. intros CM e fuel HE JN.
  pose proof (rd6_c CM e fuel HE JN) as TC. unfold st, body_regs in TC.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
         HF HPD HC FR HFR.
  replace (rd_pc 6) with 0x1389c by (vm_compute; reflexivity).
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
  { zify_cond E0. do 10 zstep.
    eapply TC with (od := od) (c := c) (rem := rem);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E0.
  do 5 zstep. in_byte0 cur c. zstep. zstep.
  if_cases E1.
  { zify_cond E1. do 8 zstep.
    eapply TC with (od := od) (c := c + 1) (rem := rem - 1);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E1.
  do 4 zstep. in_byte cur c 1. zstep. zstep. zstep.
  if_cases E2.
  { zify_cond E2. do 8 zstep.
    eapply TC with (od := od) (c := c + 2) (rem := rem - 2);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E2.
  do 4 zstep. in_byte cur c 2. zstep. zstep.
  if_cases E3.
  { zify_cond E3. do 8 zstep.
    eapply TC with (od := od) (c := c + 3) (rem := rem - 3);
      [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
      rd6_close Hcur. }
  zify_cond E3.
  do 4 zstep. in_byte cur c 3. do 8 zstep.
  eapply TC with (od := od) (c := c + 4) (rem := rem - 4);
    [ exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) | exact HF | exact HPD | .. ];
    rd6_close Hcur.
Qed.
