(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the head of the inlined owed_at (fuzz_decode.c:129-135) in
   LLVMFuzzerTestOneInput on the UBSan image, 0x12f10-0x12f5c:
     0x12f10-0x12f20  spec_msg_step (body, len, at, status & 0xff, &o.m), a4 = sp + 0x18;
     0x12f24-0x12f30  o.next = o.m.next (s5), o.status_out = o.m.status_out (s6);
     0x12f34-0x12f40  memset (&o.e, 0, 44), which zeroes o.e and o.lsb_missing (fuzz_decode.c:132-133);
     0x12f44-0x12f48  if (o.m.code != 1) -> 0x131cc, where o is owed_at (the event stays zero);
     0x12f4c-0x12f58  else memset (&o.e, 0, 40), the memset of spec_event_of (spec.h:394), and on to 0x12f5c.
   No UBSan check site is in this range. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells
  Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout spec_msg_step_c memset_c
  LLVMFuzzerTestOneInput_owed_lib.
Import ListNotations.
Open Scope Z_scope.

Lemma head_evt : spec_msg_step_contract -> memset_contract ->
  forall (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Sp lo body pos status : Z) (bb j120 j56 : list byte) (M : spec_msg) (Q : machine_state -> Prop),
    M = spec_msg_step (map bz bb) (Z.of_nat (length bb)) pos (status mod 256) ->
    seg_env Sp lo body bb -> 0 <= pos < 2 ^ 64 -> 0 <= status < 2 ^ 64 ->
    stk rsegs m lo Sp -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
    rw_cells rsegs m (Sp + 0x18) [CB 120 j120] ->
    rw_cells rsegs m (Sp + 0x150) [CB 56 j56] ->
    rw_cells rsegs m (Sp + 0x10) [C8 (Z_to_bv 64 1)] ->
    (sm_code M <> 1 ->
     owed_k Q gp tp x23 F fc m Sp lo body (Z.of_nat (length bb))
       (Owed M se_zero 0 (sm_next M) (sm_status_out M))) ->
    (sm_code M = 1 -> at_ev0 Q gp tp x23 F fc m Sp lo body bb M) ->
    evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 0x1f) (Z_to_bv 64 (Z.of_nat (length bb)))
        (Z_to_bv 64 status) x11 (Z_to_bv 64 pos) x13 x14 x15 x16 x17 (Z_to_bv 64 body) (Z_to_bv 64 (Sp + 0x50))
        (Z_to_bv 64 (2 ^ 64 - 1)) x21 x22 x23 (Z_to_bv 64 0xb0) (Z_to_bv 64 1) (Z_to_bv 64 13) (Z_to_bv 64 0x90)
        x28 x29 x30 x31)
        F (Z_to_bv 64 0x12f10) fc None m (seg_rom rsegs)).
Proof.
  intros SMS MSET x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 gp tp F fc m
    Sp lo body pos status bb j120 j56 M Q HMdef ENV Hpos Hst ST MI BA H18 H150 H10 K0 K1.
  destruct ENV as (Hlo & HloSp & HSp16 & HSp47 & Hbody & Hbb).
  pose proof (msg_ok_step (map bz bb) (Z.of_nat (length bb)) pos (status mod 256) (bytes_ok_bz bb)
    ltac:(lia) ltac:(lia) ltac:(lia)) as MOK.
  rewrite <- HMdef in MOK.
  destruct MOK as (Hcode & Hsta & Hd1 & Hd2 & Hso & Hnx & Hmsg).
  destruct (owed_split m Sp j120 H18) as (j56a & j44 & j4 & j8 & j1 & j7 & HM & HE & HP1 & HN & HS & HP2).
  clear H18.
  pose proof (munch_refl [(Sp + 0x18, Sp + 0x90); (Sp + 0x150, Sp + 0x188); (Sp - 48, Sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Hm8 : (Sp + 24) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  do 5 step.
  rewrite (unsigned_lit status) by lia.
  assert (E255 : Z.land status 255 = status mod 256)
    by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity).
  rewrite E255.
  call (sms_call SMS lo bb j56a);
    try solve [ exact Hpos | exact BA | exact HM | exact ST | exact MI | exact Hm8 | lia | left; lia
              | right; lia ].
  rewrite <- HMdef in POST.
  unfold spec_msg_cells in POST.
  (* 0x12f24-0x12f30: s5 = o.m.next, s6 = o.m.status_out, stored in o.next and o.status_out *)
  do 3 step.
  step. rewrite le1_zxb. mem_after_store.
  rewrite (zxb_b8 (sm_status_out M)) by lia.
  (* 0x12f34-0x12f40: memset (&o.e, 0, 44) *)
  do 4 step.
  call (mset_call MSET j44);
    try solve [ assumption | lia | change (Z.to_nat 44) with 44%nat; exact HE ].
  match goal with
  | H : rw_cells rsegs _ (Sp + 0x50) [CB (Z.to_nat 44) _] |- _ =>
      change (Z.to_nat 44) with 44%nat in H; destruct (mset44 _ _ H) as [HEv HLm]; clear H
  end.
  replace (Sp + 0x50 + 40) with (Sp + 0x78) in HLm by lia.
  (* 0x12f44-0x12f48: o.m.code *)
  step. rewrite (sx32_code (sm_code M)) by lia.
  step. rewrite (code_br (sm_code M)) by lia.
  destruct (Z.eqb_spec (sm_code M) 1) as [C1e|C1e]; cbn [negb]; cbv iota.
  - (* a message: the second memset and on to 0x12f5c *)
    do 4 step.
    call (mset_call MSET (repeat (b8 0) 40));
      try solve [ assumption | lia
                | change (Z.to_nat 40) with 40%nat;
                  apply (rwc_bytes rsegs _ (Sp + 0x50) _ _ HEv);
                  [vm_compute; repeat first [exact I | reflexivity | split] | vm_compute; reflexivity] ].
    match goal with
    | H : rw_cells rsegs _ (Sp + 0x50) [CB (Z.to_nat 40) _] |- _ =>
        change (Z.to_nat 40) with 40%nat in H; apply ev_zero in H; rename H into HEv2
    end.
    pose proof (K1 C1e) as K1'. unfold at_ev0 in K1'.
    apply K1' with (p1 := j4) (p2 := j7) (j56 := j56); assumption.
  - (* not a message: o is owed_at with the zero event *)
    pose proof (K0 C1e) as K0'. unfold owed_k in K0'.
    apply K0' with (p1 := j4) (p2 := j7) (j56' := j56); try assumption.
    apply (owed_join _ _ _ _ _ _ _ j4 j7);
      try solve [ exact HLm | exact HP1 | exact HN | exact HS | exact HP2 | exact HEv
                | unfold spec_msg_cells; exact POST ].
Qed.
