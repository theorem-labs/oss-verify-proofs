(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 202 of its 214 lines of code are new or changed and 681 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe diginet_ring_encode_bits.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_sysex_encode_c diginet_ring_encode_c leds_encode.
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

Ltac rr := repeat (apply rstep_range; [lia |]); lia.

(** One iteration of the loop at 0x15ae0 .. 0x15b10 (a7 = k, a4 = 6 - k, a3 = b1, a1 = b2), up to the
    `bne t0, a6` at 0x15b14. *)
Lemma ring_iter_u : forall (Q : machine_state -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask k k1 n6 n5 b1 b2 : Z),
  0 <= mask < 65536 -> 0 <= k <= 6 -> k1 = k + 1 -> n6 = 6 - k -> n5 = 5 - k ->
  0 <= b1 < 128 -> 0 <= b2 < 128 ->
  (forall t1' t2' : word,
     evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 k1) t1' t2' s0 s1 a0 (Z_to_bv 64 (rstep mask 8 k b2)) (Z_to_bv 64 mask)
                          (Z_to_bv 64 (rstep mask 1 k b1)) (Z_to_bv 64 n5) (Z_to_bv 64 1) (Z_to_bv 64 7) (Z_to_bv 64 k1)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15b14) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b2) (Z_to_bv 64 mask)
                       (Z_to_bv 64 b1) (Z_to_bv 64 n6) (Z_to_bv 64 1) (Z_to_bv 64 7) (Z_to_bv 64 k)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15ae0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask k k1 n6 n5 b1 b2
         Hm Hk -> -> -> Hb1 Hb2 K.
  do 13 zstep.
  rewrite !(ring_pick mask k 62), !(ring_pick mask k 55) by lia.
  rewrite (bv_swrap_small 32 (k + 1)) by (change (bv_half_modulus 32) with 2147483648; lia).
  replace (63 - 62 + k) with (1 + k) by lia. replace (63 - 55 + k) with (8 + k) by lia.
  replace (6 - k + -1) with (5 - k) by lia.
  rewrite (Z.lor_comm (bit_or_0 (Z.testbit mask (1 + k)) _) b1), (Z.lor_comm (bit_or_0 (Z.testbit mask (8 + k)) _) b2).
  exact (K _ _).
Qed.

(** The three payload bytes the body stores at sp+5 .. sp+7 of its frame. *)
Lemma rg_frame_pl : forall m A j x y z c1 c2 c3,
  rw_cells rsegs m A [CB 5 j; C1 x; C1 y; C1 z; C8 c1; C8 c2; C8 c3] -> bytes_at rsegs m (A + 5) [x; y; z].
Proof.
  intros m A j x y z c1 c2 c3 [[Hwf Hb] _].
  cbn [cells_bytes cbytes cells_wf cell_wf] in Hb, Hwf. destruct Hwf as [Hj _].
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hj in Hb.
  rewrite app_assoc, app_assoc in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(** diginet_sysex_encode with fn 0 and a three-byte payload: rc 0 with the eight-byte message, or a
    negative rc (E_ARG or E_RANGE). *)
Lemma rg_sysex_shape : forall dev a b c,
  (fst (sysex_spec dev 0 [a; b; c]) = 0 /\
   snd (sysex_spec dev 0 [a; b; c]) = Some ([0xf0; 0x13; dev; 0; a; b; c; 0xf7], 0, 0))
  \/ -11 <= fst (sysex_spec dev 0 [a; b; c]) <= -1.
Proof.
  intros dev a b c. unfold sysex_spec.
  destruct (0x7f <? dev).
  - right. cbv [fst E_ARG]. lia.
  - destruct (existsb (fun x => Z.testbit x 7) [a; b; c]).
    + right. match goal with |- context [fst ?p] => let v := eval vm_compute in (fst p) in change (fst p) with v end.
      lia.
    + left. split; reflexivity.
Qed.

(** The payload bytes as the callee's spec reads them. *)
Lemma rg_zb_pl : forall p0 b1 b2, 0 <= p0 < 256 -> 0 <= b1 < 128 -> 0 <= b2 < 128 ->
  zb [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 p0)); Z_to_bv 8 (bv_unsigned (Z_to_bv 64 b1));
      Z_to_bv 8 (bv_unsigned (Z_to_bv 64 b2))] = [u8 p0; b1; b2].
Proof.
  intros p0 b1 b2 H0 H1 H2. unfold zb, u8. cbn [map].
  rewrite (unsigned_lit p0), (unsigned_lit b1), (unsigned_lit b2) by lia.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small b1), (Z.mod_small b2) by lia. reflexivity.
Qed.

Theorem diginet_ring_encode_holds : diginet_sysex_encode_contract -> diginet_ring_encode_contract.
Proof.
  intros SX.
  unfold diginet_sysex_encode_contract, diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE, DIGINET_SYSEX_ENCODE_DEPTH in SX.
  unfold diginet_ring_encode_contract, diginet_ring_encode_pre, DIGINET_RING_ENCODE, DIGINET_RING_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd strip mask before (HP & HD1 & HA1 & HA2 & Hnz & HC & HAL & HSO & HMI & ST & LO).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Ra3.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  destruct HA2 as [Bm ->]. change (2 ^ 16) with 65536 in Bm.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (apply le_u32_small; exact HA1).
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (apply le_u32_big; exact HA1).
  destruct HA1 as [Bs _].
  assert (Hlen : length before = 32%nat) by (destruct HC as [[[Hw _] _] _]; cbn in Hw; lia).
  pose proof (rw_cells_bound rsegs m _ _ HC) as BO. cbn [cells_size csize] in BO.
  pose proof ST as (Lo0 & _ & _).
  assert (U32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
    by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  destruct pd as [d|].
  2: {
    (* p = NULL: E_ARG, out untouched *)
    cbn in HP. subst a0. clear HD1.
    do 7 zstep. if_true.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | exact HC] | reflexivity | exact HC]. }
  pose proof HP as HP0. destruct HP as (Hp0 & Hp8 & Hdk & Hb). destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  pose proof (HD1 d eq_refl) as D1. clear HD1. unfold disj in D1.
  cbn [bz map] in Hb.
  do 7 zstep. if_cases K0; [exfalso; zify_cond K0; lia |].
  zstep. zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
  zstep. zstep. if_cases K2; [exfalso; zify_cond K2; rewrite le_land7_mod8 in K2; lia |].
  pose proof (bytes_at_ov_read rsegs _ _ _ 1 1 Hb ltac:(cbn; lia)) as HR1.
  pose proof (bytes_at_ov_read rsegs _ _ _ 0 1 Hb ltac:(cbn; lia)) as HR0.
  cbn [firstn skipn] in HR1, HR0.
  zstep. zstep. zstep. if_cases K3.
  { (* strip >= strips: E_RANGE *)
    zify_cond K3. rewrite le_b8_unsigned in K3 by lia.
    assert (Ks : d_strips d <= strip)
      by (destruct (Z_lt_le_dec strip (2 ^ 31)) as [Hs|Hs]; [rewrite <- (Ls1 Hs); lia | lia]).
    rewrite (ring_spec_strips d strip mask Ks).
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | exact HC] | reflexivity | exact HC]. }
  zify_cond K3. rewrite le_b8_unsigned in K3 by lia.
  assert (Us : bv_unsigned a1 = strip)
    by (destruct (Z_lt_le_dec strip (2 ^ 31)) as [Hs|Hs]; [exact (Ls1 Hs) | specialize (Lb1 Hs); lia]).
  assert (Bs' : strip < d_strips d) by lia.
  zstep. zstep. if_cases K4.
  { (* mask bit 15: E_RANGE *)
    zify_cond K4. rewrite shl48_mod in K4 by lia.
    rewrite (ring_spec_mask d strip mask) by lia.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | exact HC] | reflexivity | exact HC]. }
  zify_cond K4. rewrite shl48_mod in K4 by lia.
  assert (Bm' : mask < 32768) by lia.
  do 6 zstep.
  eapply ring_iter_u with (mask := mask) (k := 0) (k1 := 1) (n6 := 6) (n5 := 5) (b1 := 0) (b2 := 0);
    [lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 1) (k1 := 2) (n6 := 5) (n5 := 4);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 2) (k1 := 3) (n6 := 4) (n5 := 3);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 3) (k1 := 4) (n6 := 3) (n5 := 2);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 4) (k1 := 5) (n6 := 2) (n5 := 1);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 5) (k1 := 6) (n6 := 1) (n5 := 0);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_true.
  eapply ring_iter_u with (mask := mask) (k := 6) (k1 := 7) (n6 := 0) (n5 := -1);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ?].
  zstep. if_false.
  match goal with |- context [Z_to_bv 64 (rstep mask 1 6 ?x)] =>
    assert (RB1 : 0 <= rstep mask 1 6 x < 128) by rr; remember (rstep mask 1 6 x) as B1 eqn:EB1 end.
  match goal with |- context [Z_to_bv 64 (rstep mask 8 6 ?x)] =>
    assert (RB2 : 0 <= rstep mask 8 6 x < 128) by rr; remember (rstep mask 8 6 x) as B2 eqn:EB2 end.
  zstep. zstep. zstep. zstep.
  rewrite shl63_shr57 by lia. rewrite Us. rewrite (Z.lor_comm (bit_or_0 _ _) strip).
  assert (RP0 : 0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256) by (apply pl0_range; lia).
  remember (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)) as P0 eqn:EP0.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  pose proof (rg_frame_pl _ _ _ _ _ _ _ _ _ FR) as HPL.
  assert (U27 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -27)) = bv_unsigned sp + -27)
    by (apply unsigned_lit; lia).
  lazymatch type of HPL with
  | bytes_at _ ?mm _ ?PL =>
      eapply evt_cut;
      [ eapply SX with (lo := lo) (dev := d_dev d) (fn := 0) (pl := PL) (before := before) | post_call rsegs mm ]
  end.
  { rewrite U27, U32.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hnz (conj HC (conj HAL
              (conj _ (conj _ (conj _ (conj HMI (conj ST _))))))))))))).
    - split; [lia | rewrite le_b8_unsigned by lia; reflexivity].
    - split; [lia | reflexivity].
    - lia.
    - replace (bv_unsigned sp + -27) with (bv_unsigned sp + -32 + 5) by lia. exact HPL.
    - reflexivity.
    - unfold disj. cbn [length]. lia.
    - lia.
    - lia.
    - lia. }
  rewrite (rg_zb_pl P0 B1 B2 RP0 RB1 RB2) in POST.
  rewrite (ring_spec_go d strip mask Bs' ltac:(lia)), ring_bits_rstep. cbn [fst snd].
  rewrite <- EB1, <- EB2, <- EP0.
  pose proof (rg_sysex_shape (d_dev d) (u8 P0) B1 B2) as SH.
  destruct (sysex_spec (d_dev d) 0 [u8 P0; B1; B2]) as [rc o] eqn:ES.
  cbn [fst snd] in SH.
  destruct POST as [HA0 POST].
  match type of HA0 with ?x = _ => subst x end.
  rewrite U32 in *. rename PC into ST.
  zstep. zstep.
  if_cases K5.
  - (* diginet_sysex_encode failed: return its rc, out as it left it *)
    destruct SH as [[Hr0 Ho] | Hr].
    { exfalso. subst rc. revert K5. vm_compute. intro HH. discriminate HH. }
    assert (WK : with_key (rc, o) (KEY 3 strip) = (rc, o)) by (destruct rc; [lia | reflexivity | reflexivity]).
    rewrite WK. clear WK.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish. all: cbn beta iota; first [split; [reflexivity | assumption] | reflexivity | assumption].
  - destruct SH as [[Hr0 Ho] | Hr].
    2: { exfalso. zify_cond K5. rewrite ?unsigned_lit_wrap in K5. lia. }
    subst rc o.
    change (with_key (0, Some ([240; 19; d_dev d; 0; u8 P0; B1; B2; 247], 0, 0)) (KEY 3 strip))
      with (0, Some ([240; 19; d_dev d; 0; u8 P0; B1; B2; 247], KEY 3 strip, 0)).
    zstep. zstep. if_cases K6; [exfalso; zify_cond K6; rewrite le_land3_mod4 in K6; lia |].
    do 5 zstep.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish. all: try reflexivity.
    rewrite Us in POST. change 65536 with (2 ^ 16) in POST. rewrite key3 in POST.
    eapply le_rekey_cells; [exact Hlen | cbn [length]; lia | exact POST].
Qed.
