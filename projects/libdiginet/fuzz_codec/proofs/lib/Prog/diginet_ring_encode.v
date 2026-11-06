(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 183 of its 199 lines of code are new or changed and 677 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells diginet_ring_encode_c diginet_ring_encode_bits.
Import ListNotations.
Open Scope Z_scope.

(** diginet_ring_encode of the plain image (0x15624, 71 instructions, sysex_encode inlined), walked
    with the tactics of Lib/Tac.v and Lib/Step.v: the NULL tests, the strips test, the mask bit-15 test,
    the 7-iteration bit loop (ring_iter, applied once per iteration), the frame of 0x10, the device
    sign test (E_ARG), the payload sign tests of the inlined sysex check (E_RANGE; b1 and b2 are 7-bit
    values, so only the first byte can fail) and the stores to out. p->device and p->strips are read
    before the first store, so the personality bytes need no disjointness from the frame. *)

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

Local Ltac rr := repeat (apply rstep_range; [lia |]); lia.

Lemma b8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (b8 z) = z.
Proof. intros z H. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma u32_reg_small : forall r v, arg_u32 r v -> v < 2 ^ 31 -> bv_unsigned r = v.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
  apply unsigned_lit. lia.
Qed.

Lemma u32_reg_big : forall r v, arg_u32 r v -> 2 ^ 31 <= v -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned r.
Proof.
  intros r v [B ->] H. unfold s32. replace (v <? 2 ^ 31) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite unsigned_lit_wrap. rewrite <- (Z_mod_plus_full (v - 2 ^ 32) 1).
  rewrite Z.mod_small by lia. lia.
Qed.

(** `lb` of a byte v, read back as unsigned: v itself below 128, at least 2^63 (negative) above. *)
Lemma sxb_cases : forall v, 0 <= v < 256 ->
  (v < 128 /\ bv_unsigned (sxb (Z_to_bv 8 v)) = v) \/ (128 <= v /\ 2 ^ 63 <= bv_unsigned (sxb (Z_to_bv 8 v))).
Proof.
  intros v Hv. unfold sxb. rewrite unsigned_lit_wrap.
  assert (S : bv_signed (Z_to_bv 8 v) = if v <? 128 then v else v - 256).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
    destruct (Z.ltb_spec v 128); Z.div_mod_to_equations; lia. }
  rewrite S. destruct (Z.ltb_spec v 128); [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

Lemma sxb_lo : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. destruct (sxb_cases v ltac:(lia)) as [[_ E] | [L _]]; [| lia].
  apply bv_eq. rewrite E. rewrite unsigned_lit by lia. reflexivity.
Qed.

(** The byte forms of the stores to out, as the bytes of the spec. *)
Lemma byte8_unsigned : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma byte_w64 : forall z, 0 <= z < 256 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof. intros z H. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma byte_zero : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)) = b8 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma byte_f7 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-9))) = b8 0xf7.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma le2_13f0 : le2 (Z_to_bv 64 5104) = [b8 0xf0; b8 0x13].
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity |]). reflexivity. Qed.

Lemma le2_8 : le2 (Z_to_bv 64 8) = [b8 8; b8 0].
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity |]). reflexivity. Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

(** One iteration of the loop at 0x1565c .. 0x15688 (t1 = k, a6 = 6 - k, a5 = b1, a4 = b2), up to the
    `bne a6, t0` at 0x1568c. *)
Lemma ring_iter : forall (Q : machine_state -> Prop) (ra sp gp tp t2 s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask k k1 n6 n5 b1 b2 : Z),
  0 <= mask < 65536 -> 0 <= k <= 6 -> k1 = k + 1 -> n6 = 6 - k -> n5 = 5 - k ->
  0 <= b1 < 128 -> 0 <= b2 < 128 ->
  (forall t2' t3' t4' : word,
     evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 k1) t2' s0 s1 a0 a1 (Z_to_bv 64 mask) a3
                          (Z_to_bv 64 (rstep mask 8 k b2)) (Z_to_bv 64 (rstep mask 1 k b1)) (Z_to_bv 64 n5) (Z_to_bv 64 1)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                     F (Z_to_bv 64 0x1568c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 k) t2 s0 s1 a0 a1 (Z_to_bv 64 mask) a3
                       (Z_to_bv 64 b2) (Z_to_bv 64 b1) (Z_to_bv 64 n6) (Z_to_bv 64 1)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1565c) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t2 s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask k k1 n6 n5 b1 b2
         Hm Hk -> -> -> Hb1 Hb2 K.
  do 12 zstep.
  rewrite !(ring_pick mask k 62), !(ring_pick mask k 55) by lia.
  rewrite (bv_swrap_small 32 (6 - k + -1)) by (change (bv_half_modulus 32) with 2147483648; lia).
  replace (63 - 62 + k) with (1 + k) by lia. replace (63 - 55 + k) with (8 + k) by lia.
  replace (6 - k + -1) with (5 - k) by lia.
  rewrite (Z.lor_comm (bit_or_0 (Z.testbit mask (1 + k)) _) b1), (Z.lor_comm (bit_or_0 (Z.testbit mask (8 + k)) _) b2).
  exact (K _ _ _).
Qed.

Theorem diginet_ring_encode_holds : diginet_ring_encode_contract.
Proof.
  unfold diginet_ring_encode_contract, diginet_ring_encode_pre, DIGINET_RING_ENCODE, DIGINET_RING_ENCODE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo pd strip mask before (HP & HA1 & HA2 & Hnz & HC & HSA & HMI & ST & LO).
  pose proof HC as HL0. destruct HL0 as [[[Hlen _] _] _].
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HA2 as [Bm ->]. change (2 ^ 16) with 65536 in Bm.
  destruct pd as [d|].
  2: {
    cbn in HP. subst a0. zstep. zstep. if_true. zstep. zstep. finish.
    cbn beta iota. split; [reflexivity | exact HC]. }
  destruct HP as [Hp0 [Hdk Hb]].
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 Hb ltac:(cbn; lia)) as HR1.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 1 Hb ltac:(cbn; lia)) as HR0.
  cbn [firstn skipn bz map] in HR1, HR0.
  assert (Ls1 : strip < 2 ^ 31 -> bv_unsigned a1 = strip) by (apply u32_reg_small; exact HA1).
  assert (Lb1 : 2 ^ 31 <= strip -> 2 ^ 64 - 2 ^ 31 <= bv_unsigned a1) by (apply u32_reg_big; exact HA1).
  destruct HA1 as [Bs _].
  destruct Hdk as (Bd0 & Bd1 & Bd2 & Bd3).
  zstep. zstep. if_cases K1; [exfalso; zify_cond K1; lia |].
  zstep. if_cases K2; [exfalso; zify_cond K2; lia |].
  zstep. zstep. zstep. if_cases K3.
  { zify_cond K3. rewrite b8_unsigned in K3 by lia.
    assert (Ks : d_strips d <= strip) by lia.
    zstep. zstep. finish. rewrite (ring_spec_strips d strip mask Ks). cbn beta iota. split; [reflexivity | exact HC]. }
  zify_cond K3. rewrite b8_unsigned in K3 by lia.
  assert (Us : bv_unsigned a1 = strip) by lia.
  assert (Bs' : strip < d_strips d) by lia.
  zstep. zstep. if_cases K4.
  { zify_cond K4. rewrite shl48_mod in K4 by lia.
    zstep. zstep. finish. rewrite (ring_spec_mask d strip mask) by lia. cbn beta iota. split; [reflexivity | exact HC]. }
  zify_cond K4. rewrite shl48_mod in K4 by lia.
  assert (Bm' : mask < 32768) by lia.
  do 6 zstep.
  eapply (ring_iter _ ra sp gp tp t2 s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask 0 1 6 5 0 0);
    [lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 1 2 5 4);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 2 3 4 3);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 3 4 3 2);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 4 5 2 1);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 5 6 1 0);
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_true.
  eapply (ring_iter _ ra sp gp tp _ s0 s1 a0 a1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m mask 6 7 0 (-1));
    [lia | lia | reflexivity | reflexivity | reflexivity | rr | rr | intros ? ? ?].
  zstep. if_false.
  match goal with |- context [Z_to_bv 64 (rstep mask 1 6 ?x)] =>
    assert (RB1 : 0 <= rstep mask 1 6 x < 128) by rr; remember (rstep mask 1 6 x) as B1 eqn:EB1 end.
  match goal with |- context [Z_to_bv 64 (rstep mask 8 6 ?x)] =>
    assert (RB2 : 0 <= rstep mask 8 6 x < 128) by rr; remember (rstep mask 8 6 x) as B2 eqn:EB2 end.
  pose proof (rw_cells_bound rsegs m _ _ HC) as BC. cbn [cells_size csize] in BC.
  pose proof ST as [Hlo [Hhi _]].
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  rewrite shl63_shr57 by lia. rewrite Us. rewrite (Z.lor_comm (bit_or_0 _ _) strip).
  assert (RP0 : 0 <= Z.lor strip (bit_or_0 (Z.testbit mask 0) 64) < 256) by (apply pl0_range; lia).
  remember (Z.lor strip (bit_or_0 (Z.testbit mask 0) 64)) as P0 eqn:EP0.
  zstep. zstep. zstep. zstep.
  unfold b8 in *.
  pose proof (sxb_cases (d_dev d) ltac:(lia)) as SXD.
  rewrite (ring_spec_go d strip mask Bs' ltac:(lia)), ring_bits_rstep. cbn [fst snd].
  rewrite <- EB1, <- EB2, <- EP0, (u8_small P0 RP0).
  if_cases K5.
  { (* device bit 7: E_ARG *)
    zify_cond K5. assert (Kd : 128 <= d_dev d) by lia.
    zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish. rewrite sysex_dev_hi by lia. cbn beta iota. split; [reflexivity | exact HC]. }
  zify_cond K5. assert (Kd : d_dev d < 128) by lia.
  rewrite (sxb_lo (d_dev d)) by lia.
  zstep. zstep. zstep. zstep.
  if_cases K6.
  { (* payload byte 0 bit 7: E_RANGE *)
    zify_cond K6. assert (Kp : 128 <= P0) by (pose proof (sxb_cases P0 RP0); lia).
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish. rewrite sysex_pl0_hi by lia. cbn beta iota. split; [reflexivity | exact HC]. }
  zify_cond K6. assert (Kp : P0 < 128) by (pose proof (sxb_cases P0 RP0); lia).
  zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K7; zify_cond K7; [exfalso; pose proof (sxb_cases B1 ltac:(lia)); lia |].
  zstep. zstep. zstep. if_true.
  zstep. zstep. if_cases K8; zify_cond K8; [exfalso; pose proof (sxb_cases B2 ltac:(lia)); lia |].
  zstep. zstep. zstep. if_false.
  do 22 zstep.
  release_frame FR ST (bv_unsigned sp).
  do 3 zstep.
  finish.
  rewrite sysex_ok by lia. cbn [with_key]. split; [reflexivity |].
  rewrite Us in HC.
  replace (Z.lor (strip mod 65536) 196608) with (KEY 3 strip) in HC by (rewrite <- key3; reflexivity).
  rewrite (byte8_unsigned P0), (byte8_unsigned B1), (byte8_unsigned B2) in HC by lia.
  rewrite (byte_w64 (d_dev d)), (byte_w64 P0), (byte_w64 B1), (byte_w64 B2), byte_zero, byte_f7 in HC by lia.
  do 32 (destruct before as [|? before]; [cbn in Hlen; lia |]).
  destruct before; [| cbn in Hlen; lia].
  eapply rw_cells_rebytes; [exact HC | cbn; split; [reflexivity | exact I] |].
  cbn [cells_bytes cbytes cmd_out bz map app firstn skipn length Z.of_nat Pos.of_succ_nat Pos.succ].
  rewrite le2_13f0, le2_8. reflexivity.
Qed.
