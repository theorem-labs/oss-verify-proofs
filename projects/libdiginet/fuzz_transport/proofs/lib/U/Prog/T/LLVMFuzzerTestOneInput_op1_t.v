(* The tail of case 1 of LLVMFuzzerTestOneInput (ubsan image), 0x13cc8 .. the call of build_and_receive at
   0x13dac: op_frame's arguments (fuzz_transport.c:1043-1049) from the bytes it read.
     0x13cc8 .. 0x13d00  w = hi << 8 | lo, then w % 1485 by the multiply 0x610f (sp+0x20), the shifts and 0xffff
                         (sp+0x28): op1_t1
     0x13d04 .. 0x13d08  len = min(w % 1485, n): op1_t2
     0x13d0c .. 0x13d7c  the UBSan pointer checks of the body and of DST[sel >> 5 & 3], SRC[sel >> 3 & 3],
                         CMD[(sel & 7) % 7] (none traps), and ack = g_last_counter when sel & 0x80, else the u16
                         read (a3): op1_t3
     0x13d80 .. 0x13dac  the two pointers from .data.rel.ro, the CMD byte from .rodata, the cursor after the take
                         (s0 / s6), send, retry, body, jal build_and_receive: op1_t4 *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_op1_k.
Import ListNotations.
Open Scope Z_scope.

Section TAIL.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* the bounds of the input buffer and of the frame, from llvm_mem *)
Ltac o1_bounds HM :=
  let HM1 := fresh "HM1" in
  pose proof HM as HM1; unfold llvm_mem in HM1;
  let Hd0 := fresh "Hd0" in let HdL := fresh "HdL" in let HD := fresh "HD" in let HLK := fresh "HLK" in
  let HSP := fresh "HSP" in let HWL := fresh "HWL" in
  destruct HM1 as (Hd0 & HdL & _ & HD & _ & _ & HLK & HSP & HWL & _);
  pose proof (bytes_at_bound rsegs _ data D HD);
  clear HD; unfold LH_K, LH_FRAME in HLK, HSP.

(* 0x13d80 .. 0x13dac: the three loads, the cursor after the take, jal build_and_receive *)
Lemma op1_t4 : forall (Q : machine_state -> Prop) m0 Sp lo ops off B F fc m j10 jio j60
    (b0 b1 b2 b3 b4 b5 w off5 n5 : Z) (ra t0 t1 t2 s0 a0 a1 a3 a5 s6 t3 t4 t5 t6 : word),
  o1_ctx data D regs0 m0 Sp lo ops B m j10 jio j60 b0 b1 b2 b3 b4 b5 off5 n5 ->
  0 <= w < 65536 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off b0 b1 b2 b3 b4 b5 w off5 n5 F fc ms' -> evt rsegs Q ms') ->
  t0 = Z_to_bv 64 139096 -> t1 = Z_to_bv 64 (8 * o1_di b0) -> t2 = Z_to_bv 64 139064 ->
  t3 = Z_to_bv 64 (8 * o1_si b0) -> t4 = Z_to_bv 64 66693 -> t5 = Z_to_bv 64 (o1_ci b0) ->
  bv_unsigned a3 mod 2 ^ 32 = o1_ack B b0 b3 b4 ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   a0 a1 (Z_to_bv 64 b1) a3 (Z_to_bv 64 (b2 * 256)) a5 (Z_to_bv 64 b5) (Z_to_bv 64 (o1_len w n5))
                   (Z_to_bv 64 0x39) (Z_to_bv 64 (data + off5)) (Z_to_bv 64 7) (Z_to_bv 64 (data + off)) s6
                   (Z_to_bv 64 n5)
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
              F (Z_to_bv 64 81280) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5 ra t0 t1 t2 s0 a0 a1 a3 a5 s6
    t3 t4 t5 t6 CTX Hw K -> -> -> -> -> -> HA3.
  destruct CTX as (Hops & Ho5 & Hn5 & H5D & Hb0 & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & HM).
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (Hd0 & HdL & _ & HD & _ & _ & HLK & HSP & HWL & MI & RE & _).
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof (o1_len_rng w n5 ltac:(lia) Hn5) as HL.
  unfold LH_K, LH_FRAME in HLK, HSP.
  do 3 step.                                 (* add t0, t0, t1; add t4, t4, t5; add t2, t2, t3 *)
  pose proof (o1_dst_rd m b0 RE) as RD. step. clear RD.     (* ld a0, 0(t0): DST[sel >> 5 & 3] *)
  pose proof (o1_src_rd m b0 RE) as RS. step. clear RS.     (* ld a1, 0(t2): SRC[sel >> 3 & 3] *)
  pose proof (o1_cmd_rd m b0 MI) as RC. step. clear RC.     (* lbu a5, 0(t4): CMD[(sel & 7) % 7] *)
  do 6 step.                                 (* add s0; sub s6; or a2; andi a4; mv a6, s3; jal build_and_receive *)
  apply K. unfold o1_post, llvm_at_bar.
  assert (LB : Z.of_nat (length (sub D off5 (Z.to_nat (o1_len w n5)))) = o1_len w n5)
    by (rewrite length_sub by lia; lia).
  rewrite LB.
  rewrite ?(unsigned_lit n5) by lia. rewrite ?(unsigned_lit (o1_len w n5)) by lia.
  rewrite ?(unsigned_lit b5) by lia. rewrite (o1_zxb_b8 (o1_cmd b0)) by apply o1_cmd_rng.
  do 13 eexists. split; [reflexivity|].
  split; [exact Hops|].
  split; [apply o1_dst_mac; exact MI|].
  split; [apply o1_src_mac; exact MI|].
  split.
  { rewrite (unsigned_lit (b2 * 256)) by lia. rewrite (unsigned_lit b1) by lia.
    rewrite o1_lor_mul by lia. rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
  split; [lia|].
  split; [exact HA3|].
  split.
  { unfold o1_ack. destruct (Z.land b0 128 =? 0); [lia|].
    unfold g_last_counter. pose proof (u_at_range B OFF_g_last_counter 4) as R.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R. }
  split.
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound b5 (2 ^ 2) ltac:(lia)). lia. }
  split; [pose proof (o1_cmd_rng b0); lia|].
  split; [apply (o1_bsub m data D off5 (Z.to_nat (o1_len w n5)) (data + off5) HD); lia|].
  split; [left; lia|].
  exact HM.
Qed.

(* 0x13d0c .. 0x13d7c *)
Lemma op1_t3 : forall (Q : machine_state -> Prop) m0 Sp lo ops off B F fc m j10 jio j60
    (b0 b1 b2 b3 b4 b5 w off5 n5 : Z) (ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7 : word),
  o1_ctx data D regs0 m0 Sp lo ops B m j10 jio j60 b0 b1 b2 b3 b4 b5 off5 n5 ->
  0 <= w < 65536 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off b0 b1 b2 b3 b4 b5 w off5 n5 F fc ms' -> evt rsegs Q ms') ->
  a7 = Z_to_bv 64 (o1_len w n5) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   (Z_to_bv 64 b0) (Z_to_bv 64 b3) (Z_to_bv 64 b1) (Z_to_bv 64 (s32_at B 64976))
                   (Z_to_bv 64 (b2 * 256)) (Z_to_bv 64 (b4 * 256)) (Z_to_bv 64 b5) a7
                   (Z_to_bv 64 0x39) (Z_to_bv 64 (data + off5)) (Z_to_bv 64 7) (Z_to_bv 64 (data + off)) s6
                   (Z_to_bv 64 n5)
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
              F (Z_to_bv 64 81164) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5 ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7
    CTX Hw K ->.
  pose proof CTX as CTX0.
  destruct CTX as (Hops & Ho5 & Hn5 & H5D & Hb0 & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & HM).
  o1_bounds HM.
  pose proof (o1_len_rng w n5 ltac:(lia) Hn5) as HL.
  step.                                      (* not t0, s3 *)
  step.                                      (* bltu t0, a7 -> trap: the body's end does not wrap *)
  o1_brf ltac:(unfold bv_ltu; rewrite (unsigned_lit (data + off5)) by lia;
               rewrite zb_lxor_ones by lia; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia).
  do 7 step.                                 (* andi t4; auipc t0; slli t1; addi t0; srli t1; slli t1; not t2 *)
  step.                                      (* bltu t2, t1 -> trap: DST + 8 * index does not wrap *)
  o1_brf ltac:(o1_bfc b0 256%positive).
  do 6 step.                                 (* slli t2; auipc t3; srli t5; addi t2; slli t3; not t5 *)
  step.                                      (* bltu t5, t3 -> trap: SRC *)
  o1_brf ltac:(o1_bfc b0 256%positive).
  do 8 step.                                 (* andi t5; auipc t4; addi t6; addi t4; seqz t6; addi t6; and t5; not t6 *)
  step.                                      (* bltu t6, t5 -> trap: CMD *)
  o1_brf ltac:(o1_bfc b0 256%positive).
  step.                                      (* slli a0, a0, 0x38 *)
  step.                                      (* bltz a0: sel & 0x80 *)
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let HB := fresh "HB" in
    assert (HB : Bool.eqb c (128 <=? b0) = true) by (o1_bfc b0 256%positive);
    apply Bool.eqb_prop in HB; rewrite HB; clear HB
  end.
  destruct (Z.leb_spec 128 b0) as [Hge|Hlt]; cbv iota.
  - (* ack = g_last_counter, a3 as loaded *)
    eapply (op1_t4 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5);
      [ exact CTX0 | exact Hw | exact K | reflexivity | o1_bfw b0 256%positive | reflexivity
      | o1_bfw b0 256%positive | reflexivity | o1_bfw b0 256%positive | ].
    unfold o1_ack. rewrite (o1_land128 b0 Hb0).
    replace (b0 <? 128) with false by (symmetry; apply Z.ltb_ge; lia). apply o1_s32.
  - step.                                    (* or a3, a5, a1: ack = the u16 read *)
    eapply (op1_t4 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5);
      [ exact CTX0 | exact Hw | exact K | reflexivity | o1_bfw b0 256%positive | reflexivity
      | o1_bfw b0 256%positive | reflexivity | o1_bfw b0 256%positive | ].
    unfold o1_ack. rewrite (o1_land128 b0 Hb0).
    replace (b0 <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (unsigned_lit (b4 * 256)) by lia. rewrite (unsigned_lit b3) by lia.
    rewrite o1_lor_mul by lia. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

(* 0x13d04 .. 0x13d08: len = min(w % 1485, n) *)
Lemma op1_t2 : forall (Q : machine_state -> Prop) m0 Sp lo ops off B F fc m j10 jio j60
    (b0 b1 b2 b3 b4 b5 w off5 n5 : Z) (ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7 : word),
  o1_ctx data D regs0 m0 Sp lo ops B m j10 jio j60 b0 b1 b2 b3 b4 b5 off5 n5 ->
  0 <= w < 65536 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off b0 b1 b2 b3 b4 b5 w off5 n5 F fc ms' -> evt rsegs Q ms') ->
  a7 = Z_to_bv 64 (w mod 1485) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   (Z_to_bv 64 b0) (Z_to_bv 64 b3) (Z_to_bv 64 b1) (Z_to_bv 64 (s32_at B 64976))
                   (Z_to_bv 64 (b2 * 256)) (Z_to_bv 64 (b4 * 256)) (Z_to_bv 64 b5) a7
                   (Z_to_bv 64 0x39) (Z_to_bv 64 (data + off5)) (Z_to_bv 64 7) (Z_to_bv 64 (data + off)) s6
                   (Z_to_bv 64 n5)
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
              F (Z_to_bv 64 81156) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5 ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7
    CTX Hw K ->.
  pose proof CTX as CTX0.
  destruct CTX as (Hops & Ho5 & Hn5 & H5D & Hb0 & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & HM).
  o1_bounds HM.
  pose proof (Z.mod_pos_bound w 1485 ltac:(lia)) as HWM.
  step.                                      (* bltu a7, s7, 8 *)
  destruct (Z.ltb_spec (w mod 1485) n5) as [Hlt|Hge].
  - o1_brt o1c.
    eapply (op1_t3 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5);
      [ exact CTX0 | exact Hw | exact K | ].
    unfold o1_len. replace (w mod 1485 <? n5) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
    reflexivity.
  - o1_brf o1c.
    step.                                    (* mv a7, s7 *)
    eapply (op1_t3 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5);
      [ exact CTX0 | exact Hw | exact K | ].
    unfold o1_len. replace (w mod 1485 <? n5) with false by (symmetry; apply Z.ltb_ge; exact Hge).
    first [ reflexivity | f_equal; lia ].
Qed.

(* 0x13cd0 .. 0x13d00: w % 1485 *)
Lemma op1_t1 : forall (Q : machine_state -> Prop) m0 Sp lo ops off B F fc m j10 jio j60
    (b0 b1 b2 b3 b4 b5 w off5 n5 : Z) (ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7 : word),
  o1_ctx data D regs0 m0 Sp lo ops B m j10 jio j60 b0 b1 b2 b3 b4 b5 off5 n5 ->
  0 <= w < 65536 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off b0 b1 b2 b3 b4 b5 w off5 n5 F fc ms' -> evt rsegs Q ms') ->
  a7 = Z_to_bv 64 w ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                   (Z_to_bv 64 b0) (Z_to_bv 64 b3) (Z_to_bv 64 b1) (Z_to_bv 64 (s32_at B 64976))
                   (Z_to_bv 64 (b2 * 256)) (Z_to_bv 64 (b4 * 256)) (Z_to_bv 64 b5) a7
                   (Z_to_bv 64 0x39) (Z_to_bv 64 (data + off5)) (Z_to_bv 64 7) (Z_to_bv 64 (data + off)) s6
                   (Z_to_bv 64 n5)
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops) t3 t4 t5 t6)
              F (Z_to_bv 64 81104) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5 ra t0 t1 t2 s0 s6 t3 t4 t5 t6 a7
    CTX Hw K ->.
  pose proof CTX as CTX0.
  destruct CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM).
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & _ & _ & _ & _ & _ & HSP & _ & _ & _ & _ & _ & _ & _ & HJ1 & HJ2 & HJ3 & FR).
  unfold LH_FRAME in HSP.
  unfold llvm_frame, llvm_saved in FR. cbn [app] in FR.
  pose proof (rw_cells_bound rsegs m Sp _ FR) as HFB.
  do 13 step.                                (* ld 0x610f; mul; srli; subw; slli; srli; add; srli; li 1485; mul; sub;
                                                ld 0xffff; and *)
  eapply (op1_t2 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 w off5 n5);
    [ exact CTX0 | exact Hw | exact K | ].
  o1_bfw w 65536%positive.
Qed.

(* 0x13cc8 .. 0x13ccc: w = hi << 8 | lo; the interface the paths of the cursor reads join at *)
Lemma op1_tail : forall (Q : machine_state -> Prop) m0 Sp lo ops off B F fc m j10 jio j60
    (b0 b1 b2 b3 b4 b5 b6 b7 off5 n5 : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  o1_ctx data D regs0 m0 Sp lo ops B m j10 jio j60 b0 b1 b2 b3 b4 b5 off5 n5 ->
  0 <= b6 < 256 -> 0 <= b7 < 256 ->
  (forall ms', o1_post data D regs0 m0 Sp lo ops B off b0 b1 b2 b3 b4 b5 (b6 + b7 * 256) off5 n5 F fc ms' ->
     evt rsegs Q ms') ->
  sp = Z_to_bv 64 Sp -> gp = reg_get regs0 3 -> tp = reg_get regs0 4 -> s1 = Z_to_bv 64 1 ->
  s2 = Z_to_bv 64 0x39 -> s4 = Z_to_bv 64 7 -> s5 = Z_to_bv 64 (data + off) ->
  s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) -> s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) ->
  s10 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) -> s11 = Z_to_bv 64 ops ->
  a3 = Z_to_bv 64 (s32_at B 64976) ->
  a0 = Z_to_bv 64 b0 -> a2 = Z_to_bv 64 b1 -> a4 = Z_to_bv 64 (b2 * 256) -> a1 = Z_to_bv 64 b3 ->
  a5 = Z_to_bv 64 (b4 * 256) -> a6 = Z_to_bv 64 b5 -> a7 = Z_to_bv 64 b6 -> t0 = Z_to_bv 64 b7 ->
  s3 = Z_to_bv 64 (data + off5) -> s7 = Z_to_bv 64 n5 ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 81096) fc None m (seg_rom rsegs)).
Proof.
  intros Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 b6 b7 off5 n5
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    CTX H6 H7 K -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  step.                                      (* slli t0, t0, 8 *)
  step.                                      (* or a7, t0, a7 *)
  eapply (op1_t1 Q m0 Sp lo ops off B F fc m j10 jio j60 b0 b1 b2 b3 b4 b5 (b6 + b7 * 256) off5 n5);
    [ exact CTX | lia | exact K | ].
  rewrite (unsigned_lit b7) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (unsigned_lit (b7 * 256)) by lia. rewrite (unsigned_lit b6) by lia.
  rewrite o1_lor_mul by lia. reflexivity.
Qed.

End TAIL.
