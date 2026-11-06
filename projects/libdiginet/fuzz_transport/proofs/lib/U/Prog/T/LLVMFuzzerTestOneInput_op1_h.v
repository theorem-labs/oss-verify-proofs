(* Case 1 of the op loop of LLVMFuzzerTestOneInput, ubsan image: the case entry 0x13b38 .. 0x13cc8 (the cursor
   reads of op_frame, fuzz_transport.c:1043-1048; U/Prog/T/LLVMFuzzerTestOneInput_op1.v states the piece).
   The eight cursor reads of op_frame (sel, send u16, ack u16, r, w u16) are inlined as one chain of byte loads
   with a UBSan pointer check before each (`addi s3, s3, 1; bgeu s1, s3 -> trap`) and an exit after each when the
   cursor runs out (n = 1 .. 8; n >= 9 reads all eight): op1_head walks each of the nine paths to 0x13cc8, where
   op1_tail (U/Prog/T/LLVMFuzzerTestOneInput_op1_t.v) takes over. The bytes past the end read as 0 (o1_byt), the
   model's fuzz_u8_m / fuzz_u16_m (U/Prog/T/LLVMFuzzerTestOneInput_op1_k.v o1_model). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op1_k LLVMFuzzerTestOneInput_op1_t.
Import ListNotations.
Open Scope Z_scope.

(* a register of the join at 0x13cc8 against op1_tail's premise: the same term; a byte of the cursor (o1b) as
   loaded (zxb), shifted (slli / slliw) or 0 past the end; the cursor after the reads (s3 / s7). The walk's kit
   folds the load address off + 1 + i to off + (1 + i) (Lib/Step.v fold_closed_in_goal); the byte index of
   o1_byt_in is put in that form before the byte's value is abstracted. *)
Ltac o1_bq :=
  unfold o1b, o1_c1;
  first [ rewrite o1_byt_out by (cbn [fi_off fi_n]; lia);
          lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply (f_equal (Z_to_bv 64)); lia end
        | rewrite o1_byt_in by (cbn [fi_off fi_n]; lia); cbn [fi_off fi_n];
          lazymatch goal with |- context [Z.to_nat (?o + 1 + ?i)] =>
            let k := eval vm_compute in (1 + i) in
            replace (o + 1 + i) with (o + k) by lia
          end;
          unfold zxb;
          lazymatch goal with |- context [bv_unsigned (nth ?k ?l ?d)] =>
            let v := fresh "v" in let Hv := fresh "Hv" in
            pose proof (o1_byte_rng (nth k l d)) as Hv;
            revert Hv; generalize (bv_unsigned (nth k l d)); intros v Hv;
            lazymatch goal with
            | |- ?a = ?a => reflexivity
            | _ => o1_bfw v 256%positive
            end
          end ].

Ltac o1_eq :=
  first [ lazymatch goal with |- ?a = ?a => reflexivity end
        | lazymatch goal with |- context [o1b] => o1_bq end
        | lazymatch goal with |- context [o1_c5] =>
            unfold o1_c5, o1_adv, o1_c1; cbn [fi_off fi_n]; apply (f_equal (Z_to_bv 64)); lia end
        | match goal with |- ?G => fail 1 "o1_eq: no rule for" G end ].

Ltac o1_ctx_tac HM :=
  unfold o1_ctx;
  repeat match goal with
  | |- llvm_mem _ _ _ _ _ _ _ _ _ _ _ => exact HM
  | |- 0 <= o1b _ _ _ _ < 256 => apply o1_byt_rng
  | |- _ /\ _ => split
  | |- _ => (unfold o1_c5, o1_adv, o1_c1; cbn [fi_off fi_n]; lia)
  end.

Section OP1.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* the input byte at data + off + k (k = i + 1: byte i of the cursor after the op byte) *)
Ltac o1_rd R off k i :=
  lazymatch goal with
  | HD : bytes_at rsegs ?mm data D |- _ =>
      pose proof (o1_rd1 mm data D (off + 1 + i) (data + off + k) HD ltac:(lia) ltac:(lia) ltac:(lia)) as R
  end.

(* the join at 0x13cc8: op1_tail with the bytes of the cursor; its register premises are left to o1_eq *)
Ltac o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K :=
  eapply (op1_tail data D regs0 Q m0 Sp lo ops off B F fc m j10 jio j60
            (o1b D off n 0) (o1b D off n 1) (o1b D off n 2) (o1b D off n 3) (o1b D off n 4)
            (o1b D off n 5) (o1b D off n 6) (o1b D off n 7) (fi_off (o1_c5 off n)) (fi_n (o1_c5 off n)));
  [ o1_ctx_tac HM | apply o1_byt_rng | apply o1_byt_rng | exact K | idtac .. ].

Lemma op1_head : forall (Q : machine_state -> Prop) m0 Sp lo ops off n B F fc m j10 jio j60
    (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  0 <= ops < OPS_MAX -> 0 <= off -> 1 <= n -> off + n <= Z.of_nat (length D) ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off (o1b D off n 0) (o1b D off n 1) (o1b D off n 2)
                 (o1b D off n 3) (o1b D off n 4) (o1b D off n 5) (o1_w D off n)
                 (fi_off (o1_c5 off n)) (fi_n (o1_c5 off n)) F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + (off + 1))) (Z_to_bv 64 7)
                   (Z_to_bv 64 (data + off)) (Z_to_bv 64 (n - 1)) (Z_to_bv 64 n)
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
              F (Z_to_bv 64 80696) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off n B F fc m j10 jio j60 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    Hops Ho Hn HnD HM K.
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (Hd0 & HdL & _ & HD & _ & _ & HLK & HSP & HWL & _ & _ & WM & _).
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  unfold LH_K, LH_FRAME in HLK, HSP.
  wk_facts.
  step.                                      (* 0x13b38 beqz s6: n = 1, no byte left *)
  destruct (Z.eq_dec n 1) as [E1|N1].
  { o1_br. do 10 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.                         (* addi s3, s3, 1; bgeu s1, s3 -> trap *)
  o1_rd R1 off 1 0. step. clear R1.              (* lbu a0, 1(s5): sel *)
  do 3 step.                                 (* addi s3, s5, 2; li a1, 2; beq s7, a1 *)
  destruct (Z.eq_dec n 2) as [E2|N2].
  { o1_br. do 9 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R2 off 2 1. step. clear R2.              (* lbu a2, 2(s5): send lo *)
  do 3 step.                                 (* addi s3, s5, 3; li a1, 3; bne s7, a1 *)
  destruct (Z.eq_dec n 3) as [E3|N3].
  { o1_br. do 9 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R3 off 3 2. step. clear R3.              (* lbu a4, 3(s5): send hi *)
  do 4 step.                                 (* addi s3, s5, 4; slli a4, a4, 8; li a1, 4; beq s7, a1 *)
  destruct (Z.eq_dec n 4) as [E4|N4].
  { o1_br. do 7 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R4 off 4 3. step. clear R4.              (* lbu a1, 4(s5): ack lo *)
  do 3 step.                                 (* addi s3, s5, 5; li a3, 5; beq s7, a3 *)
  destruct (Z.eq_dec n 5) as [E5|N5].
  { o1_br. do 6 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R5 off 5 4. step. clear R5.              (* lbu a5, 5(s5): ack hi *)
  do 5 step.                                 (* lw a3, 8(s9); addi s3, s5, 6; slliw a5, a5, 8; li a6, 6; bne s7, a6 *)
  destruct (Z.eq_dec n 6) as [E6|N6].
  { o1_br. do 6 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R6 off 6 5. step. clear R6.              (* lbu a6, 6(s5): r *)
  do 2 step.                                 (* addi s3, s5, 7; bne s7, s4 *)
  destruct (Z.eq_dec n 7) as [E7|N7].
  { o1_br. do 4 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R7 off 7 6. step. clear R7.              (* lbu a7, 7(s5): w lo *)
  do 3 step.                                 (* addi s3, s5, 8; li t0, 8; bne s7, t0 *)
  destruct (Z.eq_dec n 8) as [E8|N8].
  { o1_br. do 3 step. o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq. }
  o1_br.
  step. step. o1_br.
  o1_rd R8 off 8 7. step. clear R8.              (* lbu t0, 8(s5): w hi *)
  do 3 step.                                 (* addi s7, s7, -9; addi s3, s5, 9; j 0x13cc8 *)
  o1_fin Q m0 Sp lo ops off n B F fc m j10 jio j60 HM K. all: o1_eq.
Qed.

End OP1.
