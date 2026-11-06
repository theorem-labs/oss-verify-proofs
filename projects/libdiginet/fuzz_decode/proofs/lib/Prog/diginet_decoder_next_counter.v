(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the counter case of the sysex switch (fn 0x30, from the jump target 0x141f8): address,
   dots and the loop that stores pl[2 + k] at seg[7 - k] (diginet_decode.c:90-98).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* the eight digits counter_loop stores, seg[7 - k] = pl[2 + k] with pl = s + 3, as body bytes *)
Lemma dn_counter_loop : forall bb s seg, 0 <= s -> length seg = 8%nat ->
  counter_loop seg (map bz bb) (s + 3) 0 8 =
  [at8 bb (Z.to_nat (s + 12)); at8 bb (Z.to_nat (s + 11)); at8 bb (Z.to_nat (s + 10));
   at8 bb (Z.to_nat (s + 9)); at8 bb (Z.to_nat (s + 8)); at8 bb (Z.to_nat (s + 7));
   at8 bb (Z.to_nat (s + 6)); at8 bb (Z.to_nat (s + 5))].
Proof.
  intros bb s seg Hs L.
  do 8 (destruct seg as [|? seg]; [cbn [length] in L; lia|]).
  destruct seg; [|cbn [length] in L; lia].
  transitivity [byte_at (map bz bb) (s + 3 + 2 + 7); byte_at (map bz bb) (s + 3 + 2 + 6);
                byte_at (map bz bb) (s + 3 + 2 + 5); byte_at (map bz bb) (s + 3 + 2 + 4);
                byte_at (map bz bb) (s + 3 + 2 + 3); byte_at (map bz bb) (s + 3 + 2 + 2);
                byte_at (map bz bb) (s + 3 + 2 + 1); byte_at (map bz bb) (s + 3 + 2 + 0)];
    [reflexivity|].
  replace (s + 3 + 2 + 7) with (s + 12) by lia. replace (s + 3 + 2 + 6) with (s + 11) by lia.
  replace (s + 3 + 2 + 5) with (s + 10) by lia. replace (s + 3 + 2 + 4) with (s + 9) by lia.
  replace (s + 3 + 2 + 3) with (s + 8) by lia. replace (s + 3 + 2 + 2) with (s + 7) by lia.
  replace (s + 3 + 2 + 1) with (s + 6) by lia. replace (s + 3 + 2 + 0) with (s + 5) by lia.
  rewrite !byte_at_map_Z by lia. reflexivity.
Qed.

(* decode_sysex with the body bytes read as at8 (as diginet_decoder_next_sysex.v has it) *)
Ltac cn_model :=
  unfold decode_sysex, DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS,
    DIGINET_FN_SCRIBBLE, DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM; cbv zeta;
  rewrite !byte_at_map_Z by lia.

(* one turn of the digit loop (0x14224 .. 0x14234): lbu of body byte s + k, sb, a0 - 1, a1 + 1, bne *)
Ltac cn_turn HBB bb s k :=
  let R := fresh "RD" in
  let RB := fresh "RB" in
  pose proof (body_read rsegs _ _ bb s k HBB ltac:(lia)) as R;
  pose proof (at8_range bb (Z.to_nat (s + k))) as RB;
  step; rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (s + k)))) by lia;
  step; step; step; step; clear R RB.

Section Counter.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_counter : forall (ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra
    (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1))) (dn_e0 msg)) ->
  dm_status msg = 240 -> 1 <= dm_sysex msg -> 3 <= dm_sysex_len msg ->
  dm_sysex msg + dm_sysex_len msg < Z.of_nat (length bb) ->
  at8 bb (Z.to_nat (dm_sysex msg)) = 19 -> at8 bb (Z.to_nat (dm_sysex msg + 2)) = 48 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             (Z_to_bv 64 (dm_sysex_len msg + -3)) (Z_to_bv 64 (body + dm_sysex msg)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (dm_sysex_len msg)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT HF0 HS1 N3 HSN MK HFN.
  dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_sysex (map bz bb) msg (dn_e0 msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite HF0. reflexivity. }
  (* addi a2 = 10; bne pn, 10 *)
  step. step.
  rewrite (dn_eqb_u64 (dm_sysex_len msg + -3) 10) by lia.
  destruct (Z.eq_dec (dm_sysex_len msg + -3) 10) as [P10|P10].
  2: {
    (* another length: kind 13 and the device *)
    if_true.
    dn_fin HR HDc HD2 HE HEM; cn_model;
      rewrite MK, HFN, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb];
      rewrite (proj2 (Z.eqb_neq (dm_sysex_len msg - 3) (2 + DIGINET_COUNTER_DIGITS)))
        by (unfold DIGINET_COUNTER_DIGITS; lia); cbn [negb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  if_false.
  (* kind 11; addr = s[3]; dots = s[4]; a1 = s + 5, a0 = ev + 0x24, s0 = ev + 0x1c *)
  step. step.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 3))) as RB3.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. clear RD3.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 4 HBB ltac:(lia)) as RD4.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 4))) as RB4.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 4)))) by lia.
  step. step. clear RD4.
  step. step.
  (* the eight digits: seg[7 - k] = s[5 + k] at ev + 0x24 - k *)
  cn_turn HBB bb (dm_sysex msg) 5.
  rewrite (dn_eqb_u64 (ev + 35) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 6.
  rewrite (dn_eqb_u64 (ev + 34) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 7.
  rewrite (dn_eqb_u64 (ev + 33) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 8.
  rewrite (dn_eqb_u64 (ev + 32) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 9.
  rewrite (dn_eqb_u64 (ev + 31) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 10.
  rewrite (dn_eqb_u64 (ev + 30) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 11.
  rewrite (dn_eqb_u64 (ev + 29) (ev + 28)) by lia. if_true.
  cn_turn HBB bb (dm_sysex msg) 12.
  rewrite (dn_eqb_u64 (ev + 28) (ev + 28)) by lia. if_false.
  (* j 0x140f8 *)
  step.
  dn_fin HR HDc HD2 HE HEM; cn_model;
    rewrite MK, HFN, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb];
    rewrite (proj2 (Z.eqb_eq (dm_sysex_len msg - 3) (2 + DIGINET_COUNTER_DIGITS)))
      by (unfold DIGINET_COUNTER_DIGITS; lia); cbn [negb];
    replace (dm_sysex msg + 3 + 1) with (dm_sysex msg + 4) by lia.
  - dmsg_eq.
  - rewrite (dn_counter_loop bb (dm_sysex msg)) by first [lia | reflexivity].
    ev_head_lit. unfold DIGINET_EV_COUNTER. reflexivity.
Qed.

End Counter.
