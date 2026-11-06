(* Case 8 (the default) of the op loop of the ubsan LLVMFuzzerTestOneInput, 0x13c44 .. the jal 0x13f6c into
   receive (fuzz_transport.c:1209-1214 `default: { uint8_t pf = fuzz_u8(&in); const uint8_t *p;
   size_t n = fuzz_record(&in, &p); receive(p, n, 1, pf); }`): the poll-flags byte, then fuzz_record = fuzz_u16 then
   fuzz_take, inlined. At the case entry s3 / s6 are the cursor after the op byte (data + o + 1, n - 1) and
   s5 / s7 the cursor before it (data + o, n). Four paths reach the tail 0x13dc4:
     n = 1  (s6 = 0)      0x13db4: a3 = s7 = a0 = a1 = 0
     n = 2               pf at 1(s5) in a3, 0x13db8: s7 = a0 = a1 = 0, s3 = data + o + 2
     n = 3               pf, the low byte at 2(s5), 0x13c78 / 0x13dc0: s7 = a1 = 0, s3 = data + o + 3
     n >= 4              pf, the low byte, the high byte at 3(s5) (0x14164), s7 = n - 4, s3 = data + o + 4
   and the tail 0x13dc4 .. 0x13de8 takes t = min (hi << 8 | lo, s7) (fuzz_take), s0 = s3 + t, s6 = s7 - t (the cursor
   after the record), a0 = s3, a1 = t, a2 = 1, then j 0x13f6c: jal receive. The UBSan pointer checks are not taken:
   0 < data and data + size < 2^63. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op0_lib.
Import ListNotations.
Open Scope Z_scope.

(* The tail 0x13dc4 .. 0x13de8, 0x13f6c: a1 = a1 | a0 (the u16), t = min (a1, s7), the UBSan check of s3 + t,
   then s0 = s3 + t, s6 = s7 - t, a2 = 1, a0 = s3, j 0x13f6c, jal receive; a3 (pf) is kept. *)
Lemma op8_tail : forall (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6
    s8 s9 s10 s11 t3 t4 t5 t6 F fc m (x y q r : Z),
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= Z.lor y x < 2 ^ 16 -> 0 <= r -> 0 <= q -> q + r < 2 ^ 63 ->
  (forall t, t = (if Z.lor y x <? r then Z.lor y x else r) -> 0 <= t <= r -> t <= Z.lor y x ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 LH_RET_RECV) sp gp tp t0 t1 t2 (Z_to_bv 64 (q + t)) (Z_to_bv 64 1)
                        (Z_to_bv 64 q) (Z_to_bv 64 t) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                        s2 (Z_to_bv 64 q) s4 s5 (Z_to_bv 64 (r - t)) (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 LH_RECV) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 1) (Z_to_bv 64 x) (Z_to_bv 64 y) a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 q) s4 s5 s6 (Z_to_bv 64 r) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13dc4) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m x y q r
    Hx Hy HW Hr Hq Hqr K.
  (* 0x13dc4 or a1, a1, a0 *)
  step. rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  (* 0x13dc8 bltu a1, s7 *)
  step. rewrite (lr_ltu (Z.lor y x) r) by lia.
  destruct (Z.ltb_spec (Z.lor y x) r) as [E|E]; cbv iota.
  - (* 0x13dd0 not a0, s3; 0x13dd4 bltu a0, a1 -> trap *)
    step. rewrite (unsigned_lit q) by lia. rewrite zb_lxor_ones by lia.
    step. rewrite (lr_ltu (18446744073709551615 - q) (Z.lor y x)) by lia.
    replace (18446744073709551615 - q <? Z.lor y x) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    (* add s0, s3, a1; sub s6, s7, a1; addi a2, zero, 1; mv a0, s3; j 0x13f6c; jal receive *)
    do 6 step.
    rewrite (unsigned_lit r), (unsigned_lit (Z.lor y x)) by lia.
    apply (K (Z.lor y x)); [| lia | lia].
    replace (Z.lor y x <? r) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* 0x13dcc mv a1, s7 *)
    step.
    step. rewrite (unsigned_lit q) by lia. rewrite zb_lxor_ones by lia.
    step. rewrite (lr_ltu (18446744073709551615 - q) r) by lia.
    replace (18446744073709551615 - q <? r) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    do 6 step.
    rewrite (unsigned_lit r) by lia.
    apply (K r); [| lia | lia].
    replace (Z.lor y x <? r) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Theorem llvm_op8_holds : llvm_op_recv_stmt 8.
Proof.
  unfold llvm_op_recv_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms H.
  change (evt rsegs (recv_post data D regs0 m0 Sp lo ops c B F fc) ms).
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 &
                 m & j10 & jio & j60 & -> & HOPS & HN & HC & HC1 & HOP & HM).
  destruct c as [o n]. unfold llvm_cursor in HC. cbn [fi_off fi_n] in HN, HC.
  pose proof (lr_u8 D o n HN) as HU.
  rewrite HU in HC1, HOP. cbn [fst snd] in HC1, HOP. subst c1. cbn [fi_off fi_n].
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & _ & HD & _ & _ & HLO & HSP2 & _).
  unfold LH_K, LH_FRAME in HLO, HSP2.
  change (LH_CASE 8) with 0x13c44.
  (* 0x13c44 beqz s6 *)
  step. rewrite (lr_eqb0 (n - 1)) by lia.
  destruct (Z.eqb_spec (n - 1) 0) as [E1|E1]; cbv iota.
  { (* n = 1: 0x13db4 mv a3, zero; mv s7, zero; mv a0, zero; mv a1, zero *)
    do 4 step.
    eapply op8_tail; [lia | lia | rewrite Z.lor_0_l; lia | lia | lia | lia |].
    intros t _ Htr _. assert (Et : t = 0) by lia. subst t.
    apply evt_done.
    eapply recv_fin with (roff := o + 1) (rn := 0) (rbp := 1) (rpf := 0) (rc2 := FuzzIn (o + 1) 0);
      [ lr_side HM0 .. | ].
    intros I A k.
    apply (lr_model8 I B A D (FuzzIn o n) k (FuzzIn (o + 1) (n - 1)) (at8 D (Z.to_nat o)) (FuzzIn (o + 1) 0) 0);
      [exact HU | exact HOP | rewrite E1; apply lr_u8_0 | apply lr_rec0]. }
  (* 0x13c48 addi s3, s3, 1; 0x13c4c bgeu s1, s3 -> trap *)
  step. step. lr_notrap.
  (* 0x13c50 lbu a3, 1(s5): pf *)
  pose proof (lr_read m data D (o + 1) HD ltac:(lia) ltac:(lia)) as HR1.
  replace (data + (o + 1)) with (data + o + 1) in HR1 by lia.
  step. clear HR1.
  pose proof (lr_byte (nth (Z.to_nat (o + 1)) D (b8 0))) as RB1.
  (* 0x13c54 addi s3, s5, 2; 0x13c58 addi a0, zero, 2; 0x13c5c beq s7, a0 *)
  step. step. step.
  rewrite (lr_eqb n 2) by lia.
  destruct (Z.eqb_spec n 2) as [E2|E2]; cbv iota.
  { (* n = 2: 0x13db8 mv s7, zero; mv a0, zero; mv a1, zero *)
    do 3 step.
    eapply op8_tail; [lia | lia | rewrite Z.lor_0_l; lia | lia | lia | lia |].
    intros t _ Htr _. assert (Et : t = 0) by lia. subst t.
    apply evt_done.
    eapply recv_fin with (roff := o + 1 + 1) (rn := 0) (rbp := 1)
                         (rpf := bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0))) (rc2 := FuzzIn (o + 1 + 1) 0);
      [ lr_side HM0 .. | ].
    intros I A k.
    apply (lr_model8 I B A D (FuzzIn o n) k (FuzzIn (o + 1) (n - 1)) (at8 D (Z.to_nat o))
             (FuzzIn (o + 1 + 1) (n - 1 - 1)) (bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0))));
      [exact HU | exact HOP | apply lr_u8; lia | replace (n - 1 - 1) with 0 by lia; apply lr_rec0]. }
  (* n >= 3: 0x13c60 addi s3, s3, 1; 0x13c64 bgeu s1, s3 -> trap *)
  step. step. lr_notrap.
  (* 0x13c68 lbu a0, 2(s5): the low byte *)
  pose proof (lr_read m data D (o + 2) HD ltac:(lia) ltac:(lia)) as HR2.
  replace (data + (o + 2)) with (data + o + 2) in HR2 by lia.
  step. clear HR2.
  pose proof (lr_byte (nth (Z.to_nat (o + 2)) D (b8 0))) as RB2.
  (* 0x13c6c addi s3, s5, 3; 0x13c70 addi a1, zero, 3; 0x13c74 bne s7, a1 *)
  step. step. step.
  rewrite (lr_eqb n 3) by lia.
  destruct (Z.eqb_spec n 3) as [E3|E3]; cbn [negb]; cbv iota.
  { (* n = 3: 0x13c78 mv s7, zero; j 0x13dc0; mv a1, zero *)
    do 3 step.
    eapply op8_tail; [lia | lia | rewrite Z.lor_0_l; lia | lia | lia | lia |].
    intros t _ Htr _. assert (Et : t = 0) by lia. subst t.
    apply evt_done.
    eapply recv_fin with (roff := o + 1 + 1 + 1) (rn := 0) (rbp := 1)
                         (rpf := bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0))) (rc2 := FuzzIn (o + 1 + 1 + 1) 0);
      [ lr_side HM0 .. | ].
    intros I A k.
    apply (lr_model8 I B A D (FuzzIn o n) k (FuzzIn (o + 1) (n - 1)) (at8 D (Z.to_nat o))
             (FuzzIn (o + 1 + 1) (n - 1 - 1)) (bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0))));
      [exact HU | exact HOP | apply lr_u8; lia | replace (n - 1 - 1) with 1 by lia; apply lr_rec1]. }
  (* n >= 4: 0x14164 addi s3, s3, 1; 0x14168 bgeu s1, s3 -> trap *)
  step. step. lr_notrap.
  (* 0x1416c lbu a1, 3(s5): the high byte *)
  pose proof (lr_read m data D (o + 3) HD ltac:(lia) ltac:(lia)) as HR3.
  replace (data + (o + 3)) with (data + o + 3) in HR3 by lia.
  step. clear HR3.
  pose proof (lr_byte (nth (Z.to_nat (o + 3)) D (b8 0))) as RB3.
  (* 0x14170 addi s7, s7, -4; 0x14174 addi s3, s5, 4; 0x14178 slli a1, a1, 8; 0x1417c j 0x13dc4 *)
  do 4 step.
  rewrite lr_zxb.
  pose proof (lr_lor (bv_unsigned (nth (Z.to_nat (o + 2)) D (b8 0)))
                (bv_unsigned (nth (Z.to_nat (o + 3)) D (b8 0))) RB2 RB3) as HW.
  eapply op8_tail;
    [ lia | rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia | rewrite HW; lia
    | lia | lia | lia | ].
  intros t Ht Htr Htw. rewrite HW in Htw.
  apply evt_done.
  eapply recv_fin with (roff := o + 1 + 1 + 2) (rn := t) (rbp := 1)
                       (rpf := bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0)))
                       (rc2 := FuzzIn (o + 1 + 1 + 2 + t) (n - 1 - 1 - 2 - t));
    [ lr_side HM0 .. | ].
  intros I A k.
  apply (lr_model8 I B A D (FuzzIn o n) k (FuzzIn (o + 1) (n - 1)) (at8 D (Z.to_nat o))
           (FuzzIn (o + 1 + 1) (n - 1 - 1)) (bv_unsigned (nth (Z.to_nat (o + 1)) D (b8 0))));
    [exact HU | exact HOP | apply lr_u8; lia | apply (lr_rec2 D (o + 1 + 1) (n - 1 - 1) t); [lia|] ].
  replace (o + 1 + 1 + 1) with (o + 3) by lia. replace (o + 1 + 1) with (o + 2) by lia. lr_teq Ht.
Qed.
