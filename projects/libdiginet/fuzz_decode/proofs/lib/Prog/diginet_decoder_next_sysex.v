(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the sysex path from 0x13f38: the length and maker
   tests, the device, and the switch on the function byte fn through the jump table at 0x103e4
   (decode_sysex inlined, diginet_decode.c:37-105). The table index is (fn >> 4) | (fn << 28 as a
   32-bit int), at most 7 exactly when fn is one of 0x00, 0x10, .., 0x70; the entries 5 and 6
   (0x50, 0x60) go to the default, as fn values decode_sysex has no case for. The cases of the
   strip LEDs (0x1416c) and the system byte (0x14194) are walked here, the others in
   diginet_decoder_next_ring.v, _meter.v, _counter.v and _scribble.v.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  memcpy_c diginet_meter_segments_c diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib
  diginet_decoder_next_ring diginet_decoder_next_meter diginet_decoder_next_counter diginet_decoder_next_scribble.
Import ListNotations.
Open Scope Z_scope.

(* the table index the code computes from fn (0x13f64 .. 0x13f6c) *)
Definition dn_idx (fn : Z) : Z :=
  Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 fn)) 28))))
        (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 fn)) 4))).

(* a byte other than the eight multiples of 16 below 128 takes the bltu to the default *)
Lemma dn_idx_other : forall fn, 0 <= fn < 256 ->
  fn <> 0 -> fn <> 16 -> fn <> 32 -> fn <> 48 -> fn <> 64 -> fn <> 80 -> fn <> 96 -> fn <> 112 ->
  bv_ltu (Z_to_bv 64 7) (Z_to_bv 64 (dn_idx fn)) = true.
Proof.
  intros fn Hfn N0 N1 N2 N3 N4 N5 N6 N7.
  assert (H : forall z, 0 <= z < 2^8 ->
            (existsb (Z.eqb z) [0; 16; 32; 48; 64; 80; 96; 112] || bv_ltu (Z_to_bv 64 7) (Z_to_bv 64 (dn_idx z)))
            = true).
  { apply (byte_forall (fun z => existsb (Z.eqb z) [0; 16; 32; 48; 64; 80; 96; 112] ||
                                 bv_ltu (Z_to_bv 64 7) (Z_to_bv 64 (dn_idx z)))).
    vm_compute. reflexivity. }
  specialize (H fn Hfn). cbn [existsb] in H.
  rewrite (proj2 (Z.eqb_neq _ _) N0), (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2),
    (proj2 (Z.eqb_neq _ _) N3), (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_neq _ _) N5),
    (proj2 (Z.eqb_neq _ _) N6), (proj2 (Z.eqb_neq _ _) N7) in H.
  cbn [orb] in H. exact H.
Qed.

(* decode_sysex with the body bytes read as at8 *)
Ltac sx_model :=
  unfold decode_sysex, DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS,
    DIGINET_FN_SCRIBBLE, DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM; cbv zeta;
  rewrite !byte_at_map_Z by lia.

Section Sysex.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_sysex : memcpy_contract -> diginet_meter_segments_contract ->
  forall (ra' t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra (dn_e0 msg) ->
  dm_status msg = 240 -> 1 <= dm_sysex msg -> 0 <= dm_sysex_len msg ->
  dm_sysex msg + dm_sysex_len msg < Z.of_nat (length bb) ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) s1' a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f38) fc None m1 (seg_rom rsegs)).
Proof.
  intros MCPY SEG ra' t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m1 HCTX HAT HF0 HS1 HN0 HSN.
  pose proof HCTX as HCTX0. dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_sysex (map bz bb) msg (dn_e0 msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite HF0. reflexivity. }
  (* ld s2 = sysex_len; s1 = 1; bltu s2, 3 *)
  step. step. step.
  step.
  rewrite (ltu_lit (dm_sysex_len msg) 3) by lia.
  destruct (Z.ltb_spec (dm_sysex_len msg) 3) as [N3|N3].
  { (* fewer than 3 payload bytes: kind 13 *)
    dn_fin HR HDc HD2 HE HEM;
      unfold decode_sysex; cbv zeta; rewrite (proj2 (Z.ltb_lt _ _) N3); cbn [orb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  (* ld a1 = the payload; lbu the maker *)
  step.
  rewrite (sysex_ptr_nz body (dm_sysex msg)) by lia.
  pose proof (body_read rsegs m1 body bb (dm_sysex msg) 0 HBB ltac:(lia)) as RD0.
  pose proof (body_read rsegs m1 body bb (dm_sysex msg) 1 HBB ltac:(lia)) as RD1.
  replace (dm_sysex msg + 0) with (dm_sysex msg) in RD0 by lia.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg))) as RB0.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 1))) as RB1.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 2))) as RB2.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg)))) by lia.
  step. step.
  rewrite (dn_eqb_int64 (at8 bb (Z.to_nat (dm_sysex msg))) 19) by lia.
  destruct (Z.eq_dec (at8 bb (Z.to_nat (dm_sysex msg))) 19) as [MK|MK].
  2: {
    (* another maker: kind 13 *)
    if_true.
    dn_fin HR HDc HD2 HE HEM;
      unfold decode_sysex, DIGINET_SYSEX_MAKER; cbv zeta; rewrite (byte_at_map_Z bb (dm_sysex msg)) by lia;
      rewrite (proj2 (Z.eqb_neq _ _) MK), (proj2 (Z.ltb_ge _ _) N3); cbn [orb negb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  if_false.
  (* lbu the device and store it; lbu fn; the table index *)
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 1)))) by lia.
  step.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 2 HBB ltac:(lia)) as RD2.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 2)))) by lia.
  step. step. step. step.
  step.
  remember (at8 bb (Z.to_nat (dm_sysex msg + 2))) as fn eqn:Hfn.
  assert (HAT1 : dn_at sp m0 _ d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra
                   (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1))) (dn_e0 msg)))
    by (unfold dn_at; repeat (split; [eassumption|]); eassumption).
  (* the event of every case but the five walked further: kind 13 and the device *)
  assert (HRD : forall fn', fn' = fn -> fn' <> 0 -> fn' <> 16 -> fn' <> 32 -> fn' <> 48 -> fn' <> 64 ->
            fn' <> 112 ->
            res = (1, de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1)))
                        (de_set_kind DIGINET_EV_OTHER (dn_e0 msg)),
                   {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { intros fn' -> N0 N1 N2 N3' N4 N7. rewrite HR. f_equal. f_equal. sx_model.
    rewrite <- Hfn, MK, (proj2 (Z.ltb_ge _ _) N3). cbn [Z.eqb Pos.eqb orb negb].
    rewrite (proj2 (Z.eqb_neq _ _) N0), (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2),
      (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_neq _ _) N3'), (proj2 (Z.eqb_neq _ _) N7).
    reflexivity. }
  destruct (Z.eq_dec fn 0) as [F0|F0].
  { (* the ring *)
    rewrite F0 in *. if_false. do 7 step. step.
    eapply dn_ring; [exact HCTX0 | exact HAT1 | lia | lia | lia | lia | exact MK | symmetry; exact Hfn]. }
  destruct (Z.eq_dec fn 16) as [F1|F1].
  { (* the meter *)
    rewrite F1 in *. if_false. do 7 step. step.
    eapply dn_meter; [exact SEG | exact HCTX0 | exact HAT1 | lia | lia | lia | lia | exact MK | symmetry; exact Hfn]. }
  destruct (Z.eq_dec fn 48) as [F3|F3].
  { (* the counter *)
    rewrite F3 in *. if_false. do 7 step. step.
    eapply dn_counter; [exact HCTX0 | exact HAT1 | lia | lia | lia | lia | exact MK | symmetry; exact Hfn]. }
  destruct (Z.eq_dec fn 64) as [F4|F4].
  { (* the scribble strip *)
    rewrite F4 in *. if_false. do 7 step. step.
    eapply dn_scribble; [exact MCPY | exact HCTX0 | exact HAT1 | lia | lia | lia | lia | exact MK | symmetry; exact Hfn]. }
  clear HAT1.
  destruct (Z.eq_dec fn 32) as [F2|F2].
  { (* the strip LEDs: two payload bytes after the function *)
    rewrite F2 in *. if_false. do 7 step. step.
    step. step.
    rewrite (dn_eqb_u64 (dm_sysex_len msg + -3) 2) by lia.
    destruct (Z.eq_dec (dm_sysex_len msg + -3) 2) as [P2|P2].
    - if_false.
      step. step.
      pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
      pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 3))) as RB3.
      step.
      rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
      step. step.
      pose proof (body_read rsegs _ body bb (dm_sysex msg) 4 HBB ltac:(lia)) as RD4.
      pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 4))) as RB4.
      step.
      rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 4)))) by lia.
      step. step.
      dn_fin HR HDc HD2 HE HEM; sx_model;
        rewrite <- Hfn, MK, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb];
        rewrite (proj2 (Z.eqb_eq (dm_sysex_len msg - 3) 2)) by lia; cbn [negb];
        replace (dm_sysex msg + 3 + 1) with (dm_sysex msg + 4) by lia.
      + dmsg_eq.
      + ev_head_lit. unfold DIGINET_EV_STRIP_LEDS. reflexivity.
    - if_true.
      dn_fin HR HDc HD2 HE HEM; sx_model;
        rewrite <- Hfn, MK, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb];
        rewrite (proj2 (Z.eqb_neq (dm_sysex_len msg - 3) 2)) by lia; cbn [negb].
      + dmsg_eq.
      + ev_head_lit. reflexivity. }
  destruct (Z.eq_dec fn 112) as [F7|F7].
  { (* the system byte *)
    rewrite F7 in *. if_false. do 7 step. step.
    step. step. step.
    dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite <- Hfn, MK, (proj2 (Z.ltb_ge _ _) N3); cbn [Z.eqb Pos.eqb orb negb].
    - dmsg_eq.
    - ev_head_lit. unfold DIGINET_EV_SYSTEM. reflexivity. }
  specialize (HRD fn eq_refl F0 F1 F2 F3 F4 F7).
  destruct (Z.eq_dec fn 80) as [F5|F5].
  { (* 0x50: the table's default *)
    rewrite F5 in *. if_false. do 7 step. step.
    dn_fin HRD HDc HD2 HE HEM.
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  destruct (Z.eq_dec fn 96) as [F6|F6].
  { (* 0x60: the table's default *)
    rewrite F6 in *. if_false. do 7 step. step.
    dn_fin HRD HDc HD2 HE HEM.
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  (* any other byte: the bltu to the default *)
  change (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 fn)) 28))))
                (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 fn)) 4)))) with (dn_idx fn).
  rewrite (dn_idx_other fn) by lia.
  dn_fin HRD HDc HD2 HE HEM.
  - dmsg_eq.
  - ev_head_lit. reflexivity.
Qed.

End Sysex.
