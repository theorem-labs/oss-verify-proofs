(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the control-change family of the inlined spec_event_of (spec.h:412-427) with
   the fader's LSB lookahead (fuzz_decode.c:137-149) in LLVMFuzzerTestOneInput on the UBSan image,
   0x12f70-0x12ff0, 0x13164-0x13180, 0x1319c-0x131a0 and 0x131a4-0x131c8:
     0x12f70-0x12f74  a0 = m.d1; d1 > 0x1f -> 0x13164;
     0x12f78-0x12f88  the fader: e.kind = SPEC_EV_FADER (1), e.strip = d1, e.value = d2 << 3;
     0x12f8c-0x12fa0  spec_msg_step (body, len, o.next, o.status_out, &lsb), a4 = sp + 0x150;
     0x12fa4-0x12fc4  lsb.code == 1, (lsb.status & 0xf0) == 0xb0, lsb.d1 == 0x20 + m.d1, else -> 0x1319c;
     0x12fc8-0x12ff0  e.value |= lsb.d2 >> 4 & 7 (the `slli 57` / `srli 61` pair), o.next = lsb.next,
                      o.status_out = lsb.status_out;
     0x1319c-0x131a0  o.lsb_missing = 1;
     0x13164-0x13180  d1 == 0x5c: the jog, e.delta = d2 - 0x40;
     0x131a4-0x131c8  d1 - 0x40 (as a byte) <= 0x17: the V-Pot, e.strip = d1 - 0x40, e.delta = d2 - 0x40; else
                      the event stays OTHER and the walk goes on at 0x131cc.
   No UBSan check site is in this range. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout spec_msg_step_c
  LLVMFuzzerTestOneInput_owed_lib.
Import ListNotations.
Open Scope Z_scope.

Lemma cc_evt : spec_msg_step_contract ->
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    seg_env Sp lo body bb -> msg_ok (Z.of_nat (length bb)) M ->
    Z.land (sm_status M) 240 = 176 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (owed_tail (map bz bb) (Z.of_nat (length bb)) M) ->
    at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x12f70.
Proof.
  intros SMS gp tp x23 F fc m0 Sp lo body bb M Q ENV MOK Hfam K.
  destruct ENV as (Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb).
  destruct MOK as (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg).
  assert (Hlen : 0 <= Z.of_nat (length bb) < 2 ^ 64) by lia.
  unfold at_ev1. intros y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m p1 p2 j56
    MU WM MI ST BA HM HEv HLm HP1 HN HS HP2 H150 H10.
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  step. rewrite (zxb_b8 (sm_d1 M)) by lia.
  step. rewrite (bltu_lit 31 (sm_d1 M)) by lia.
  destruct (Z.ltb_spec 31 (sm_d1 M)) as [Hgt|Hle]; cbv iota.
  - (* 0x13164: not a fader *)
    rewrite (owed_tail_cc (map bz bb) (Z.of_nat (length bb)) M Hfam ltac:(lia)) in K.
    rewrite (seo_cc (map bz bb) M Hfam) in K.
    replace (sm_d1 M <? 32) with false in K by (symmetry; apply Z.ltb_ge; lia).
    cbv iota in K.
    step.
    step. rewrite (beq_lit (sm_d1 M) 92) by lia.
    destruct (Z.eqb_spec (sm_d1 M) 92) as [Hjog|Hjog]; cbn [negb]; cbv iota.
    + (* 0x1316c-0x13180: the jog *)
      replace (s16 (sm_d2 M - 64)) with (sm_d2 M + -64) in K
        by (unfold s16; rewrite (Z.mod_small (sm_d2 M - 64 + 32768)) by lia; lia).
      step. rewrite (zxb_b8 (sm_d2 M)) by lia.
      do 2 step. usub.
      do 2 step.
      step.
      apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
      apply (owed_join _ _ _ _ _ _ _ p1 p2);
        try solve [ assumption | unfold spec_msg_cells; exact HM ].
      all: try (rewrite ev_cells_unfold; exact HEv).
    + (* 0x131a4: the V-Pot, or OTHER *)
      step. usub.
      step. rewrite (land255_addw (sm_d1 M) (-64)) by lia.
      step.
      assert (Hm256 : 0 <= (sm_d1 M + -64) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
      step. rewrite (bltu_lit 23 ((sm_d1 M + -64) mod 256)) by lia.
      assert (Evp : (23 <? (sm_d1 M + -64) mod 256) = negb ((64 <=? sm_d1 M) && (sm_d1 M <? 88))).
      { destruct (Z_le_gt_dec 64 (sm_d1 M)) as [Hv|Hv].
        - rewrite (Z.mod_small (sm_d1 M + -64) 256) by lia.
          destruct (Z.ltb_spec 23 (sm_d1 M + -64)); destruct (Z.leb_spec 64 (sm_d1 M));
            destruct (Z.ltb_spec (sm_d1 M) 88); cbn [andb negb]; first [reflexivity | exfalso; lia].
        - replace ((sm_d1 M + -64) mod 256) with (sm_d1 M + -64 + 256)
            by (rewrite <- (Z.mod_unique (sm_d1 M + -64) 256 (-1) (sm_d1 M + -64 + 256)) by lia; reflexivity).
          destruct (Z.ltb_spec 23 (sm_d1 M + -64 + 256)); destruct (Z.leb_spec 64 (sm_d1 M));
            cbn [andb negb]; first [reflexivity | exfalso; lia]. }
      rewrite Evp.
      destruct ((64 <=? sm_d1 M) && (sm_d1 M <? 88)) eqn:Evpot; cbn [negb]; cbv iota.
      * (* 0x131b4-0x131c8: the V-Pot *)
        replace (u8 (sm_d1 M - 64)) with (sm_d1 M + -64) in K
          by (unfold u8; rewrite Z.mod_small;
              [lia | apply andb_true_iff in Evpot; destruct Evpot as [E1 E2];
                     apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia]).
        replace (s16 (sm_d2 M - 64)) with (sm_d2 M + -64) in K
          by (unfold s16; rewrite (Z.mod_small (sm_d2 M - 64 + 32768)) by lia; lia).
        step. rewrite (zxb_b8 (sm_d2 M)) by lia.
        step. usub.
        do 2 step.
        step. rewrite le1_lit. mem_after_store.
        step.
        apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
        apply (owed_join _ _ _ _ _ _ _ p1 p2);
          try solve [ assumption | unfold spec_msg_cells; exact HM ].
        all: try (rewrite ev_cells_unfold; exact HEv).
      * (* the event stays OTHER *)
        apply K with (p1 := p1) (p2 := p2) (j56' := j56); try assumption.
        apply (owed_join _ _ _ _ _ _ _ p1 p2);
          try solve [ assumption | unfold spec_msg_cells; exact HM ].
        all: try (rewrite ev_cells_unfold; exact HEv).
  - (* 0x12f78: the fader *)
    rewrite (owed_tail_fader (map bz bb) (Z.of_nat (length bb)) M Hfam ltac:(lia)) in K.
    cbv zeta in K.
    pose proof (msg_ok_step (map bz bb) (Z.of_nat (length bb)) (sm_next M) (sm_status_out M)
      (bytes_ok_bz bb) ltac:(lia) ltac:(lia) ltac:(lia)) as LOK.
    remember (spec_msg_step (map bz bb) (Z.of_nat (length bb)) (sm_next M) (sm_status_out M)) as L eqn:HLdef.
    destruct LOK as (Lcode & Lsta & Ld1 & Ld2 & Lso & Lnx & Lmsg).
    assert (HX : 0 <= Z.shiftl (sm_d2 M) 3 < 2048) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (u16 (Z.shiftl (sm_d2 M) 3)) with (Z.shiftl (sm_d2 M) 3) in K
      by (unfold u16; rewrite Z.mod_small; [reflexivity | lia]).
    step. rewrite (zxb_b8 (sm_d2 M)) by lia.
    step. usub.
    step.
    step. rewrite le1_lit. mem_after_store.
    step.
    do 6 step.
    call (sms_call SMS lo bb j56);
      try solve [ exact BA | exact ST | exact MI | exact H150 | lia | left; lia | right; lia
                | Z.div_mod_to_equations; lia ].
    match goal with
    | H : rw_cells rsegs _ (Sp + 0x150) (spec_msg_cells _) |- _ =>
        rewrite <- HLdef in H; unfold spec_msg_cells in H
    end.
    step. rewrite (sx32_code (sm_code L)) by lia.
    step. rewrite (code_br (sm_code L)) by lia.
    destruct (Z.eqb_spec (sm_code L) 1) as [Lc1|Lc1]; cbn [negb]; cbv iota.
    + step. rewrite (zxb_b8 (sm_status L)) by lia.
      step. usub.
      pose proof (land_b (sm_status L) 240 ltac:(lia) ltac:(lia)) as Lfam.
      step. rewrite (beq_lit (Z.land (sm_status L) 240) 176) by lia.
      destruct (Z.eqb_spec (Z.land (sm_status L) 240) 176) as [Lf176|Lf176]; cbn [negb]; cbv iota.
      * step. rewrite (zxb_b8 (sm_d1 M)) by lia.
        step. rewrite (zxb_b8 (sm_d1 L)) by lia.
        step. usub.
        step. rewrite (beq_lit (sm_d1 M + 32) (sm_d1 L)) by lia.
        destruct (Z.eqb_spec (sm_d1 M + 32) (sm_d1 L)) as [Ld|Ld]; cbn [negb]; cbv iota.
        -- (* the LSB is the fader's: merge it *)
           replace (sm_code L =? 1) with true in K by (symmetry; apply Z.eqb_eq; exact Lc1).
           replace (Z.land (sm_status L) 240 =? 176) with true in K
             by (symmetry; apply Z.eqb_eq; exact Lf176).
           replace (sm_d1 L =? 32 + sm_d1 M) with true in K by (symmetry; apply Z.eqb_eq; lia).
           cbn [andb] in K. cbv iota in K. cbn [se_value] in K.
           assert (HY : 0 <= Z.land (Z.shiftr (sm_d2 L) 4) 7 < 8).
           { rewrite Z.land_comm. change 8 with (2 ^ 3).
             apply land_lt_pow2; [lia | apply Z.shiftr_nonneg; lia]. }
           assert (HL16 : 0 <= Z.lor (Z.shiftl (sm_d2 M) 3) (Z.land (Z.shiftr (sm_d2 L) 4) 7) < 2 ^ 16)
             by (apply lor_lt_pow2; lia).
           replace (u16 (Z.lor (Z.shiftl (sm_d2 M) 3) (u16 (Z.land (Z.shiftr (sm_d2 L) 4) 7))))
             with (Z.lor (Z.shiftl (sm_d2 M) 3) (Z.land (Z.shiftr (sm_d2 L) 4) 7)) in K
             by (unfold u16; rewrite (Z.mod_small (Z.land (Z.shiftr (sm_d2 L) 4) 7)) by lia;
                 rewrite Z.mod_small by lia; reflexivity).
           step. rewrite (zxb_b8 (sm_d2 L)) by lia.
           do 2 step.
           rewrite (sx16_small (Z.shiftl (sm_d2 M) 3)) by lia.
           step.
           step. usub.
           step. rewrite (shl57_shr61 (sm_d2 L)) by lia.
           step. usub.
           do 2 step.
           step. rewrite le1_zxb. mem_after_store.
           step.
           match goal with
           | H : rw_cells rsegs ?mm (Sp + 336) (_ :: _) |- _ =>
               destruct (rw_cells_forget rsegs mm (Sp + 336) _ H) as [jl HJl]
           end.
           cbn [cells_size csize Nat.add] in HJl.
           apply K with (p1 := p1) (p2 := p2) (j56' := jl); try assumption.
           apply (owed_join _ _ _ _ _ _ _ p1 p2);
             try solve [ assumption | unfold spec_msg_cells; exact HM ].
           all: try (rewrite ev_cells_unfold; exact HEv).
        -- (* 0x1319c: no LSB *)
           replace (sm_d1 L =? 32 + sm_d1 M) with false in K by (symmetry; apply Z.eqb_neq; lia).
           rewrite andb_false_r in K. cbv iota in K.
           do 2 step.
           match goal with
           | H : rw_cells rsegs ?mm (Sp + 336) (_ :: _) |- _ =>
               destruct (rw_cells_forget rsegs mm (Sp + 336) _ H) as [jl HJl]
           end.
           cbn [cells_size csize Nat.add] in HJl.
           apply K with (p1 := p1) (p2 := p2) (j56' := jl); try assumption.
           apply (owed_join _ _ _ _ _ _ _ p1 p2);
             try solve [ assumption | unfold spec_msg_cells; exact HM ].
           all: try (rewrite ev_cells_unfold; exact HEv).
      * replace (Z.land (sm_status L) 240 =? 176) with false in K
          by (symmetry; apply Z.eqb_neq; exact Lf176).
        rewrite andb_false_r, andb_false_l in K. cbv iota in K.
        do 2 step.
        match goal with
        | H : rw_cells rsegs ?mm (Sp + 336) (_ :: _) |- _ =>
            destruct (rw_cells_forget rsegs mm (Sp + 336) _ H) as [jl HJl]
        end.
        cbn [cells_size csize Nat.add] in HJl.
        apply K with (p1 := p1) (p2 := p2) (j56' := jl); try assumption.
        apply (owed_join _ _ _ _ _ _ _ p1 p2);
          try solve [ assumption | unfold spec_msg_cells; exact HM ].
        all: try (rewrite ev_cells_unfold; exact HEv).
    + replace (sm_code L =? 1) with false in K by (symmetry; apply Z.eqb_neq; exact Lc1).
      cbn [andb] in K. cbv iota in K.
      do 2 step.
      match goal with
      | H : rw_cells rsegs ?mm (Sp + 336) (_ :: _) |- _ =>
          destruct (rw_cells_forget rsegs mm (Sp + 336) _ H) as [jl HJl]
      end.
      cbn [cells_size csize Nat.add] in HJl.
      apply K with (p1 := p1) (p2 := p2) (j56' := jl); try assumption.
      apply (owed_join _ _ _ _ _ _ _ p1 p2);
        try solve [ assumption | unfold spec_msg_cells; exact HM ].
      all: try (rewrite ev_cells_unfold; exact HEv).
Qed.
