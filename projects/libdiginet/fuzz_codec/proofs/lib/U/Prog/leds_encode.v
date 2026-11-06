(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 180 of its 199 lines of code are new or changed and 674 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_sysex_encode_c leds_encode_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma le_land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma le_land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma le_b8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof. intros z H. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma le_u32_small : forall r v, arg_u32 r v -> v < 2 ^ 31 -> bv_unsigned r = v.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  apply unsigned_lit. lia.
Qed.

Lemma le_u32_big : forall r v, arg_u32 r v -> 2 ^ 31 <= v -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned r.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full (v - 2 ^ 32) 1).
  rewrite Z.mod_small by lia. lia.
Qed.

(** The two payload bytes leds_encode stores at sp+6, sp+7 of its frame. *)
Lemma le_frame_pl : forall m A j x y c1 c2 c3,
  rw_cells rsegs m A [CB 6 j; C1 x; C1 y; C8 c1; C8 c2; C8 c3] -> bytes_at rsegs m (A + 6) [x; y].
Proof.
  intros m A j x y c1 c2 c3 [[Hwf Hb] _].
  cbn [cells_bytes cbytes cells_wf cell_wf] in Hb, Hwf. destruct Hwf as [Hj _].
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hj in Hb.
  rewrite app_assoc in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(** diginet_sysex_encode with fn 0x20 and a two-byte payload: rc 0 with the seven-byte message, or a
    negative rc (E_ARG or E_RANGE). *)
Lemma le_sysex_shape : forall dev a b,
  (fst (sysex_spec dev 32 [a; b]) = 0 /\
   snd (sysex_spec dev 32 [a; b]) = Some ([0xf0; 0x13; dev; 32; a; b; 0xf7], 0, 0))
  \/ -11 <= fst (sysex_spec dev 32 [a; b]) <= -1.
Proof.
  intros dev a b. unfold sysex_spec.
  destruct (0x7f <? dev).
  - right. cbv [fst E_ARG]. lia.
  - destruct (existsb (fun x => Z.testbit x 7) [a; b]).
    + right. match goal with |- context [fst ?p] => let v := eval vm_compute in (fst p) in change (fst p) with v end.
      lia.
    + left. split; reflexivity.
Qed.

(** The payload bytes as the callee's spec reads them. *)
Lemma le_zb_pl : forall addr (r : word) bits, 0 <= addr < 2 ^ 16 -> bv_unsigned r = bits ->
  zb [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 addr)); Z_to_bv 8 (bv_unsigned r)] = [u8 addr; u8 bits].
Proof.
  intros addr r bits Ha Hr. unfold zb, u8. cbn [map]. rewrite unsigned_lit by lia. rewrite Hr.
  rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(** The key leds_encode stores: addr | 0x50000 = DIGINET_KEY(5, addr) for addr < 2^16. *)
Lemma le_key : forall addr, 0 <= addr < 2 ^ 16 -> Z.lor addr 327680 = KEY 5 addr.
Proof.
  intros addr Ha. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(** The first 28 bytes of a command (all but the key). *)
Definition le_head (before : list byte) (bs : list Z) (dp : Z) : list byte :=
  bz bs ++ skipn (length bs) (firstn 24 before) ++ bz [Z.of_nat (length bs); dp] ++ firstn 2 (skipn 26 before).

Lemma le_cmd_out_split : forall before bs k dp,
  cmd_out before (Some (bs, k, dp)) = le_head before bs dp ++ le4 (Z_to_bv 64 k).
Proof. intros. cbv beta iota delta [cmd_out le_head]. rewrite <- !app_assoc. reflexivity. Qed.

Lemma le_head_length : forall before bs dp, length before = 32%nat -> (length bs <= 24)%nat ->
  length (le_head before bs dp) = 28%nat.
Proof.
  intros before bs dp Hb Hbs. unfold le_head, bz.
  rewrite !length_app, !length_map, length_skipn, length_firstn, length_firstn, length_skipn, Hb.
  cbn [length]. lia.
Qed.

(** The 32 bytes of out after the key store over a successful diginet_sysex_encode. *)
Lemma le_rekey_cells : forall m A before bs k k' dp,
  length before = 32%nat -> (length bs <= 24)%nat ->
  rw_cells rsegs m A [CB 28 (firstn 28 (cmd_out before (Some (bs, k, dp)))); C4 (Z_to_bv 64 k')] ->
  rw_cells rsegs m A [CB 32 (cmd_out before (Some (bs, k', dp)))].
Proof.
  intros m A before bs k k' dp Hb Hbs H.
  pose proof (le_head_length before bs dp Hb Hbs) as LP.
  rewrite (le_cmd_out_split before bs k dp) in H. rewrite (le_cmd_out_split before bs k' dp).
  assert (F28 : firstn 28 (le_head before bs dp ++ le4 (Z_to_bv 64 k)) = le_head before bs dp)
    by (rewrite <- LP; apply firstn_app_exact).
  rewrite F28 in H.
  destruct H as [[Hwf Hbt] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_app, length_le4, LP; reflexivity | exact I].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *. exact Hbt.
  - cbn [cells_size csize] in *. exact Hw.
Qed.

Theorem leds_encode_holds : diginet_sysex_encode_contract -> leds_encode_contract.
Proof.
  intros SX.
  unfold diginet_sysex_encode_contract, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE, DIGINET_SYSEX_ENCODE_DEPTH in SX.
  unfold leds_encode_contract, leds_encode_pre, LEDS_ENCODE, LEDS_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo d addr bits before (HP & D1 & HAD & HA1 & HA2 & Hnz & HC & HAL & HSO & HMI & ST & LO).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Ra3.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  assert (Lb2s : bits < 2 ^ 31 -> bv_unsigned a2 = bits) by (apply le_u32_small; exact HA2).
  assert (Lb2b : 2 ^ 31 <= bits -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a2) by (apply le_u32_big; exact HA2).
  destruct HA2 as [Bb _].
  pose proof HP as HP0. destruct HP as (Hp0 & Hp8 & Hdk & Hb). destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  cbn [bz map] in Hb. unfold disj in D1.
  subst a1.
  assert (Hlen : length before = 32%nat) by (destruct HC as [[[Hw _] _] _]; cbn in Hw; lia).
  pose proof (rw_cells_bound rsegs m _ _ HC) as BO. cbn [cells_size csize] in BO.
  pose proof ST as (Lo0 & _ & _).
  assert (U32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
    by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K0.
  2: {
    (* bits > 0x7f: E_RANGE, out untouched *)
    zify_cond K0.
    assert (Hbig : 0x7f < bits)
      by (destruct (Z_lt_le_dec bits (2 ^ 31)) as [Hs|Hs]; [rewrite <- (Lb2s Hs); lia | lia]).
    replace (leds_spec d addr bits) with (E_RANGE, @None cmd)
      by (unfold leds_spec; replace (0x7f <? bits) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | exact HC] | reflexivity | exact HC]. }
  zify_cond K0.
  assert (Ub : bv_unsigned a2 = bits)
    by (destruct (Z_lt_le_dec bits (2 ^ 31)) as [Hs|Hs]; [exact (Lb2s Hs) | specialize (Lb2b Hs); lia]).
  assert (Hsmall : bits <= 0x7f) by lia.
  zstep. zstep. zstep. zstep.
  if_cases K1; [exfalso; zify_cond K1; rewrite le_land7_mod8 in K1; lia |].
  pose proof (bytes_at_ov_read rsegs _ _ _ 0 1 Hb ltac:(cbn; lia)) as HR.
  cbn [firstn skipn] in HR.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof (le_frame_pl _ _ _ _ _ _ _ _ FR) as HPL.
  assert (U26 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -26)) = bv_unsigned sp + -26)
    by (apply unsigned_lit; lia).
  lazymatch type of HPL with
  | bytes_at _ _ _ ?PL =>
      eapply evt_cut;
      [ eapply SX with (lo := lo) (dev := d_dev d) (fn := 32) (pl := PL) (before := before) | post_call rsegs m0 ]
  end.
  { rewrite U26, U32.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hnz (conj HC (conj HAL
              (conj _ (conj _ (conj _ (conj HMI (conj ST _))))))))))))).
    - split; [lia | rewrite le_b8_unsigned by lia; reflexivity].
    - split; [lia | reflexivity].
    - lia.
    - replace (bv_unsigned sp + -26) with (bv_unsigned sp + -32 + 6) by lia. exact HPL.
    - reflexivity.
    - unfold disj. cbn [length]. lia.
    - lia.
    - lia.
    - lia. }
  rewrite (le_zb_pl addr a2 bits HAD Ub) in POST.
  pose proof (le_sysex_shape (d_dev d) (u8 addr) (u8 bits)) as SH.
  destruct (sysex_spec (d_dev d) 32 [u8 addr; u8 bits]) as [rc o] eqn:ES.
  cbn [fst snd] in SH.
  destruct POST as [HA0 POST].
  match type of HA0 with ?x = _ => subst x end.
  assert (EL : leds_spec d addr bits = with_key (rc, o) (KEY 5 addr))
    by (unfold leds_spec; replace (0x7f <? bits) with false by (symmetry; apply Z.ltb_ge; lia); rewrite ES; reflexivity).
  rewrite EL. clear EL.
  rewrite U32 in *. rename PC into ST.
  zstep.
  if_cases K2.
  - (* diginet_sysex_encode failed: return its rc, out as it left it *)
    destruct SH as [[Hr0 Ho] | Hr].
    { exfalso. subst rc. revert K2. vm_compute. intro HH. discriminate HH. }
    assert (WK : with_key (rc, o) (KEY 5 addr) = (rc, o)) by (destruct rc; [lia | reflexivity | reflexivity]).
    rewrite WK. clear WK.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | assumption] | reflexivity | assumption].
  - destruct SH as [[Hr0 Ho] | Hr].
    2: { exfalso. zify_cond K2. rewrite ?unsigned_lit_wrap in K2. lia. }
    subst rc o.
    change (with_key (0, Some ([240; 19; d_dev d; 32; u8 addr; u8 bits; 247], 0, 0)) (KEY 5 addr))
      with (0, Some ([240; 19; d_dev d; 32; u8 addr; u8 bits; 247], KEY 5 addr, 0)).
    zstep. zstep.
    if_cases K3; [exfalso; zify_cond K3; rewrite le_land3_mod4 in K3; lia |].
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: try reflexivity.
    eapply le_rekey_cells; [exact Hlen | cbn [length]; lia | ].
    rewrite (le_key addr HAD) in POST. exact POST.
Qed.
