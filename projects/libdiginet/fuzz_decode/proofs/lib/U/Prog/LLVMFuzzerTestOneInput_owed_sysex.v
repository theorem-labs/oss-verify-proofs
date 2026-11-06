(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the system exclusive part of the inlined spec_event_of (spec.h:428-499) in
   LLVMFuzzerTestOneInput on the UBSan image, from 0x1302c (a0 = m.status, the event OTHER at sp + 0x50) to
   0x131cc:
     0x1302c-0x13030  status != 0xf0 -> 0x131cc (spec.h:428, the event stays OTHER);
     0x13034-0x1304c  s = body + m.sysex_at, with the UBSan checks of its addition (0x1303c, wrap) and of its null
                      arithmetic (0x1304c, (s == 0) xor (body != 0), the flag at sp + 0x10);
     0x13050-0x13058  sysex_len < 3 -> 0x131cc (spec.h:431);
     0x1305c-0x13068  UBSan beqz body, s[0] != SPEC_MAKER -> 0x131cc (spec.h:431);
     0x1306c-0x13074  UBSan beq s, -1, e.device = s[1] (spec.h:434);
     0x13078-0x13084  the UBSan wrap checks of s + 3 and s + 2;
     0x13088-0x1309c  fn = s[2] rotated right by 4 in 32 bits (`srli 4`, `slliw 28`, `or`), > 7 -> 0x131cc (fn is not
                      a multiple of 0x10 below 0x80: spec.h:499);
     0x130a0-0x130c0  the jump through the table at 0x103a4 with a0 = pl = s + 3, a3 = pn = sysex_len - 3: 0 ring
                      0x130c4, 1 meter 0x13268, 2 LEDs 0x13230, 3 counter 0x132f0, 4 scribble 0x13344, 5 and 6
                      0x131cc (spec.h:499), 7 system 0x1325c;
     0x1325c-0x13264  the system case: e.kind = SPEC_EV_SYSTEM (12) (spec.h:493-495).
   The other cases are LLVMFuzzerTestOneInput_owed_sysex_{ring,meter,leds,counter,scrib}.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout memcpy_c
  LLVMFuzzerTestOneInput_owed_lib LLVMFuzzerTestOneInput_owed_sysex_lib LLVMFuzzerTestOneInput_owed_sysex_ring
  LLVMFuzzerTestOneInput_owed_sysex_meter LLVMFuzzerTestOneInput_owed_sysex_leds
  LLVMFuzzerTestOneInput_owed_sysex_counter LLVMFuzzerTestOneInput_owed_sysex_scrib.
Import ListNotations.
Open Scope Z_scope.

Ltac dstep := step; fold_closed_z.

(* a case of the jump table: the case lemma KC at its entry *)
Ltac sx_enter KC :=
  unfold at_sx in KC;
  eapply KC; [ first [ reflexivity | f_equal; lia ] .. | sx_mem_solve ].

Lemma sysex_evt : memcpy_contract ->
  forall (gp tp x23 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
         (Sp lo body : Z) (bb : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    seg_env Sp lo body bb -> msg_ok (Z.of_nat (length bb)) M -> sm_code M = 1 ->
    Z.land (sm_status M) 240 <> 144 -> Z.land (sm_status M) 240 <> 176 ->
    owed_k Q gp tp x23 F fc m0 Sp lo body (Z.of_nat (length bb))
      (owed_tail (map bz bb) (Z.of_nat (length bb)) M) ->
    at_ev1 Q gp tp x23 F fc m0 Sp lo body bb M 0x1302c.
Proof.
  intros MCPY gp tp x23 F fc m0 Sp lo body bb M Q ENV MOK Hc1 Hn144 Hn176 K.
  rewrite (owed_tail_sx _ _ _ Hn144 Hn176) in K.
  pose proof ENV as ENV0. pose proof MOK as MOK0.
  destruct ENV as (Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb).
  destruct MOK as (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg).
  destruct (Hmsg Hc1) as (Hnxl & Hsx0 & Hsn0 & Hsxn).
  unfold at_ev1. intros y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m p1 p2 j56
    MU WM MI ST BA HM HEv HLm HP1 HN HS HP2 H150 H10.
  unfold spec_msg_cells in HM. rewrite ev_cells_unfold in HEv.
  (* 0x1302c-0x13030: status != 0xf0 -> 0x131cc *)
  do 2 step.
  rewrite (beq_lit (sm_status M) 240) by lia.
  destruct (Z.eqb_spec (sm_status M) 240) as [E240|E240]; cbn [negb]; cbv iota.
  2: { rewrite (seo_plain _ M Hn144 Hn176 E240) in K. sx_fin K. }
  (* 0x13034-0x1304c: s = body + m.sysex_at; UBSan: the addition does not wrap, and s != 0 as body != 0 *)
  do 3 step. take false.
  step. rewrite (seqz_pos (body + sm_sysex_at M)) by lia.
  do 3 step. take false.
  (* 0x13050-0x13058: sysex_len < 3 -> 0x131cc *)
  do 3 step.
  rewrite (bltu_lit (sm_sysex_len M) 3) by lia.
  destruct (Z.ltb_spec (sm_sysex_len M) 3) as [L3|L3]; cbv iota.
  { rewrite (seo_sx_short _ M E240 L3) in K. sx_fin K. }
  (* 0x1305c: UBSan body != 0; 0x13060-0x13068: s[0] != SPEC_MAKER -> 0x131cc *)
  step. take false.
  rd_step (sm_sysex_at M).
  rewrite (zxb_b8 _ (bat_range bb (sm_sysex_at M))).
  do 2 step.
  pose proof (bat_range bb (sm_sysex_at M)) as Rmk.
  rewrite (beq_lit (byte_at (map bz bb) (sm_sysex_at M)) 19) by lia.
  destruct (Z.eqb_spec (byte_at (map bz bb) (sm_sysex_at M)) 19) as [Hmk|Hmk]; cbn [negb]; cbv iota.
  2: { rewrite (seo_sx_maker _ M E240 L3 Hmk) in K. sx_fin K. }
  (* 0x1306c: UBSan s + 1 does not wrap; 0x13070-0x13074: e.device = s[1] *)
  step. take false.
  rd_step (sm_sysex_at M + 1).
  step. rewrite le1_zxb. mem_after_store.
  (* 0x13078-0x13084: UBSan s + 3 and s + 2 do not wrap *)
  do 2 step. take false.
  do 2 step. take false.
  (* 0x13088-0x1309c: fn rotated right by 4 in 32 bits *)
  rd_step (sm_sysex_at M + 2).
  rewrite (zxb_b8 _ (bat_range bb (sm_sysex_at M + 2))).
  remember (byte_at (map bz bb) (sm_sysex_at M + 2)) as fn eqn:Hfn.
  assert (Rfn : 0 <= fn < 256) by (subst fn; apply bat_range).
  do 5 step.
  assert (SXE : sx_env Sp lo body bb M) by exact (conj ENV0 (conj MOK0 (conj Hc1 (conj E240 (conj L3 Hmk))))).
  assert (D : fn = 0 \/ fn = 16 \/ fn = 32 \/ fn = 48 \/ fn = 64 \/ fn = 80 \/ fn = 96 \/ fn = 112 \/
              ~ (fn mod 16 = 0 /\ fn < 128)) by lia.
  destruct D as [D|[D|[D|[D|[D|[D|[D|[D|D]]]]]]]];
    [ rewrite D in Hfn |- *; take false; do 9 dstep .. | ].
  - (* 0x00 ring: 0x130c4 *)
    pose proof (sx_ring_evt gp tp x23 F fc m0 Sp lo body bb M Q SXE (eq_sym Hfn) K) as KC. sx_enter KC.
  - (* 0x10 meter: 0x13268 *)
    pose proof (sx_meter_evt gp tp x23 F fc m0 Sp lo body bb M Q SXE (eq_sym Hfn) K) as KC. sx_enter KC.
  - (* 0x20 LEDs: 0x13230 *)
    pose proof (sx_leds_evt gp tp x23 F fc m0 Sp lo body bb M Q SXE (eq_sym Hfn) K) as KC. sx_enter KC.
  - (* 0x30 counter: 0x132f0 *)
    pose proof (sx_counter_evt gp tp x23 F fc m0 Sp lo body bb M Q SXE (eq_sym Hfn) K) as KC. sx_enter KC.
  - (* 0x40 scribble: 0x13344 *)
    pose proof (sx_scrib_evt MCPY gp tp x23 F fc m0 Sp lo body bb M Q SXE (eq_sym Hfn) K) as KC. sx_enter KC.
  - (* 0x50: the table's entry 5 is 0x131cc *)
    rewrite (seo_sx_other _ M E240 L3 Hmk) in K by (rewrite <- Hfn; lia). sx_fin K.
  - (* 0x60: the table's entry 6 is 0x131cc *)
    rewrite (seo_sx_other _ M E240 L3 Hmk) in K by (rewrite <- Hfn; lia). sx_fin K.
  - (* 0x70 system: 0x1325c-0x13264, e.kind = SPEC_EV_SYSTEM *)
    do 3 step.
    rewrite (seo_system _ M E240 L3 Hmk (eq_sym Hfn)) in K. sx_fin K.
  - (* fn is not a multiple of 0x10 below 0x80: the rotation is above 7, 0x1309c -> 0x131cc *)
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let P := eval pattern fn in c in
      lazymatch P with ?f fn =>
        assert (Hc : forall z, 0 <= z < 256 -> implb (negb ((z mod 16 =? 0) && (z <? 128))) (f z) = true)
          by exact (enum256 (fun z => implb (negb ((z mod 16 =? 0) && (z <? 128))) (f z))
                      ltac:(vm_compute; reflexivity));
        assert (Hcf : c = true)
      end
    end.
    { pose proof (Hc fn Rfn) as H1.
      replace ((fn mod 16 =? 0) && (fn <? 128)) with false in H1
        by (symmetry; destruct (Z.eqb_spec (fn mod 16) 0); destruct (Z.ltb_spec fn 128); cbn [andb];
            first [ reflexivity | exfalso; apply D; split; assumption ]).
      exact H1. }
    rewrite Hcf; cbv iota.
    rewrite (seo_sx_other _ M E240 L3 Hmk) in K by (rewrite <- Hfn; lia). sx_fin K.
Qed.
