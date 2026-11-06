(* Case 1 of the op loop of LLVMFuzzerTestOneInput in the plain image (fuzz_transport.c:1172-1174
   `case 1: op_frame(&in); break;`, op_frame inlined, fuzz_transport.c:1032-1047; TModel/TOps.v
   LLVMFuzzerTestOneInput_op_m's `op =? 1` branch: op_frame_m I B D (A k) c1, and the receive index goes to S k).
   The machine, from tr6/llvmf-plain.dis (all CFG-reachable code from 0x139ec to the latch 0x1428c):
     0x139ec-0x1431c  op_frame's 8 input reads (sel; send lo, hi; ack lo, hi; r; w lo, hi), unrolled per cursor
                      length: 0x13b4c (no byte), 0x139fc / 0x13c94 / 0x13f1c / 0x14160 (1 to 4 bytes) into
                      0x14164, 0x142bc / 0x142e0 / 0x14300 / 0x14310 (5 to 8 or more) into 0x1417c; a3 =
                      g_last_counter (lw 8(s9) at 0x14174 / 0x142ac)
     0x1417c-0x14184  ack = sel & 0x80 ? g_last_counter : ack0 (bltz on sel << 56)
     0x14188-0x141c8  w % 1485 (a multiply by the frame constant 0x610f at sp + 0x18, masked by 0xffff at
                      sp + 0x20), the take's n = min(want, n) (bltu)
     0x141cc-0x14234  send = hi << 8 | lo; DST[], SRC[] (rel32 tables at 0x104b8, 0x1049c), CMD[] (0x10495)
     0x14238          jal build_and_receive (0x15be4, Prog/T/build_and_receive_c.v), ra 0x1423c
     0x1423c-0x14288  j 0x14288; mv s3, s0 (the cursor after the take), on into the latch 0x1428c.
   The evt walk to the call is llvm_op1_walk; the case as an SR step (the call is an SR contract) is
   llvm_op1_sr, on the SR program points of LLVMFuzzerTestOneInput_sr.v. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TNeed TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_disp.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YK11 YK0s YK0o YM05 YM06 YO0d YL00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require MemNorm AllocSlots.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require receive_c build_and_receive_c TSRGlue
  LLVMFuzzerTestOneInput_sr LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the read-only tables op_frame reads (fuzz_transport.c:1034-1038), at their image addresses ---- *)

(* n bytes of the image's read-only data, read through any memory mem_inv holds of *)
Lemma op1_rom : forall m A n bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> length bs = n ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> ov_read_bytes rsegs m (Z_to_bv 64 A) n = Some bs.
Proof.
  intros m A n bs HI Hb Hl HA HAn. subst n.
  pose proof (ro_cells_image rsegs m A bs HI Hb HA HAn) as R.
  apply (ro_cells_read_at rsegs m A [CB (length bs) bs] 0 (CB (length bs) bs) (length bs) (Z_to_bv 64 A) R);
    [reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.

(* op_frame's DST[] (sel >> 5 & 3): the rel32 table at 0x104b8 (auipc 0x141d4 - 0x4000 + 0x2e4) holds
   [-56; -44; 16; -56], so the pointers are 0x10480 (HOST), 0x1048c (SPEC_BCAST), 0x104c8 (OTHER), 0x10480 *)
Definition op1_dstp (sel : Z) : Z := nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) [0x10480; 0x1048c; 0x104c8; 0x10480] 0.
(* op_frame's SRC[] (sel >> 3 & 3): the rel32 table at 0x1049c (auipc 0x141fc - 0x4000 + 0x2a0) holds
   [-22; 16; -28; 22], so the pointers are 0x10486 (DESK), 0x104ac (DESK2), 0x10480 (HOST), 0x104b2 (NOTDD) *)
Definition op1_srcp (sel : Z) : Z := nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) [0x10486; 0x104ac; 0x10480; 0x104b2] 0.
(* op_frame's CMD[] ((sel & 7) % 7): the bytes at 0x10495 (auipc 0x141f0 - 0x4000 + 0x2a5) *)
Definition op1_cmd (sel : Z) : Z := nth (Z.to_nat (Z.land sel 7 mod 7)) op_frame_CMD 0.

(* every byte value, by computation *)
Lemma op1_byte_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> P x = true.
Proof.
  intros P H x Hx. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

(* every pair of byte values, by computation *)
Lemma op1_pair_all : forall (P : Z -> Z -> bool),
  forallb (fun h => forallb (fun l => P h l) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true ->
  forall h l, 0 <= h < 256 -> 0 <= l < 256 -> P h l = true.
Proof.
  intros P H h l Hh Hl. rewrite forallb_forall in H.
  assert (Ih : In h (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat h). split; [lia|]. apply in_seq. lia. }
  specialize (H h Ih). rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat l). split; [lia|]. apply in_seq. lia.
Qed.

(* ---- the model: op_frame_m's reads, a byte at a time ----
   op_frame reads 8 bytes after the op byte (sel; send lo, hi; ack lo, hi; r; w lo, hi), each 0 once the cursor is
   empty (fuzz.h:40-46). op1_g D c j is the byte j places on from cursor c (0 past its end), op1_adv c t the
   cursor t bytes on (stopping at the end). *)
Definition op1_g (D : list byte) (c : fuzz_in) (j : Z) : Z :=
  if j <? fi_n c then bv_unsigned (nth (Z.to_nat (fi_off c + j)) D (b8 0)) else 0.
Definition op1_adv (c : fuzz_in) (t : Z) : fuzz_in :=
  FuzzIn (fi_off c + Z.min t (fi_n c)) (fi_n c - Z.min t (fi_n c)).

(* fuzz_transport.c:1045: the take's n, and the cursor after it *)
Definition op1_len (D : list byte) (cA : fuzz_in) : Z :=
  Z.min ((Z.lor (op1_g D cA 6) (Z.shiftl (op1_g D cA 7) 8) mod 2 ^ 16) mod 1485) (fi_n (op1_adv cA 8)).
Definition op1_c6 (D : list byte) (cA : fuzz_in) : fuzz_in :=
  FuzzIn (fi_off (op1_adv cA 8) + op1_len D cA) (fi_n (op1_adv cA 8) - op1_len D cA).

Lemma op1_g_range : forall D c j, 0 <= op1_g D c j < 256.
Proof.
  intros D c j. unfold op1_g. destruct (j <? fi_n c); [|lia].
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (fi_off c + j)) D (b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma op1_u8 : forall D c t, 0 <= t -> 0 <= fi_n c ->
  fuzz_u8_m D (op1_adv c t) = (op1_adv c (t + 1), op1_g D c t).
Proof.
  intros D c t Ht Hn. unfold fuzz_u8_m, op1_adv, op1_g. cbn [fi_off fi_n].
  destruct (Z.ltb_spec t (fi_n c)) as [L|L].
  - rewrite (Z.min_l t) by lia. rewrite (Z.min_l (t + 1)) by lia.
    destruct (Z.eqb_spec (fi_n c - t) 0) as [E|E]; [lia|].
    unfold at8, bz. f_equal. f_equal; lia.
  - rewrite (Z.min_r t) by lia. rewrite (Z.min_r (t + 1)) by lia.
    destruct (Z.eqb_spec (fi_n c - fi_n c) 0) as [E|E]; [reflexivity | lia].
Qed.

Lemma op1_u16 : forall D c t, 0 <= t -> 0 <= fi_n c ->
  fuzz_u16_m D (op1_adv c t) = (op1_adv c (t + 2), Z.lor (op1_g D c t) (Z.shiftl (op1_g D c (t + 1)) 8) mod 2 ^ 16).
Proof.
  intros D c t Ht Hn. unfold fuzz_u16_m. rewrite (op1_u8 D c t Ht Hn), (op1_u8 D c (t + 1) ltac:(lia) Hn).
  replace (t + 1 + 1) with (t + 2) by lia. reflexivity.
Qed.

Lemma op1_adv0 : forall c, 0 <= fi_n c -> op1_adv c 0 = c.
Proof. intros [o n] H. unfold op1_adv. cbn [fi_off fi_n] in *. rewrite Z.min_l by lia. f_equal; lia. Qed.

(* fuzz_transport.c:1032-1047 op_frame, as the reads above give its values *)
Lemma op1_frame_eq : forall I B D a cA, 0 <= fi_n cA ->
  op_frame_m I B D a cA =
    match build_and_receive_m I B a (nth (Z.to_nat (Z.land (Z.shiftr (op1_g D cA 0) 5) 3)) op_frame_DST [])
            (nth (Z.to_nat (Z.land (Z.shiftr (op1_g D cA 0) 3) 3)) op_frame_SRC [])
            (Z.lor (op1_g D cA 1) (Z.shiftl (op1_g D cA 2) 8) mod 2 ^ 16)
            (if Z.land (op1_g D cA 0) 0x80 =? 0 then Z.lor (op1_g D cA 3) (Z.shiftl (op1_g D cA 4) 8) mod 2 ^ 16
             else g_last_counter B)
            (Z.land (op1_g D cA 5) 3) (op1_cmd (op1_g D cA 0))
            (sub D (fi_off (op1_adv cA 8)) (Z.to_nat (op1_len D cA))) with
    | Some (B1, _) => Some (B1, op1_c6 D cA)
    | None => None
    end.
Proof.
  intros I B D a cA Hn.
  assert (E0 : fuzz_u8_m D cA = (op1_adv cA 1, op1_g D cA 0)).
  { pose proof (op1_u8 D cA 0 ltac:(lia) Hn) as E. rewrite op1_adv0 in E by exact Hn. exact E. }
  assert (E1 : fuzz_u16_m D (op1_adv cA 1) =
               (op1_adv cA 3, Z.lor (op1_g D cA 1) (Z.shiftl (op1_g D cA 2) 8) mod 2 ^ 16))
    by exact (op1_u16 D cA 1 ltac:(lia) Hn).
  assert (E2 : fuzz_u16_m D (op1_adv cA 3) =
               (op1_adv cA 5, Z.lor (op1_g D cA 3) (Z.shiftl (op1_g D cA 4) 8) mod 2 ^ 16))
    by exact (op1_u16 D cA 3 ltac:(lia) Hn).
  assert (E3 : fuzz_u8_m D (op1_adv cA 5) = (op1_adv cA 6, op1_g D cA 5))
    by exact (op1_u8 D cA 5 ltac:(lia) Hn).
  assert (E4 : fuzz_u16_m D (op1_adv cA 6) =
               (op1_adv cA 8, Z.lor (op1_g D cA 6) (Z.shiftl (op1_g D cA 7) 8) mod 2 ^ 16))
    by exact (op1_u16 D cA 6 ltac:(lia) Hn).
  unfold op_frame_m.
  rewrite E0; cbv beta iota zeta. rewrite E1; cbv beta iota zeta. rewrite E2; cbv beta iota zeta.
  rewrite E3; cbv beta iota zeta. rewrite E4; cbv beta iota zeta.
  unfold fuzz_take_m. cbv beta iota zeta.
  change (SPEC_MAX_BODY + 1) with 1485.
  replace (if (Z.lor (op1_g D cA 6) (Z.shiftl (op1_g D cA 7) 8) mod 2 ^ 16) mod 1485 <? fi_n (op1_adv cA 8)
           then (Z.lor (op1_g D cA 6) (Z.shiftl (op1_g D cA 7) 8) mod 2 ^ 16) mod 1485
           else fi_n (op1_adv cA 8)) with (op1_len D cA)
    by (unfold op1_len; match goal with |- context [if ?x <? ?y then _ else _] =>
          destruct (Z.ltb_spec x y); lia end).
  reflexivity.
Qed.

Section OP1.
Context (data : Z) (D : list byte).

(* The state at the call of build_and_receive (0x14238 jal, so pc 0x15be4 and ra 0x1423c), from the registers
   the common tail starts with (TAIL, 0x1417c): a0 = DST[], a1 = SRC[], a2 = send, a3 = ack, a4 = retry,
   a5 = CMD[], a6 = the body (the cursor before the take), a7 = len (the take's n); s0 / s6 the cursor after
   the take. *)
Definition op1_call (Sp ops : Z) (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m : word -> option byte)
    (sel : Z) (wa1 wa2 wa3 wa4 : word) (cF : fuzz_in) (len : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 w19 w20 w23 t3 t4 t5 t6 : word) (dstp srcp cmd : Z),
    ms = MS (mkR (Z_to_bv 64 0x1423c) (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 (data + fi_off cF + len))
                 (Z_to_bv 64 7) (Z_to_bv 64 dstp) (Z_to_bv 64 srcp)
                 (Z_to_bv 64 (Z.lor (bv_unsigned wa2) (bv_unsigned wa1))) wa3 wa4 (Z_to_bv 64 cmd)
                 (Z_to_bv 64 (data + fi_off cF)) (Z_to_bv 64 len) (Z_to_bv 64 0x39) w19 w20
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n cF - len)) w23 (Z_to_bv 64 1)
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x15be4) fc None m (seg_rom rsegs) /\
    dstp mod 2 ^ 64 = op1_dstp sel /\ srcp mod 2 ^ 64 = op1_srcp sel /\ cmd = op1_cmd sel.

(* 0x141cc-0x14238: send = a2 | a1, the three table reads, the take's cursor, the call *)
Lemma llvm_op1_t3 : forall Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x5 x6 e2 r8 wa1 wa2 wa3 wa4 x15 x16 w20 w22 e3 e4 e5 e6 cF sel len (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D cF -> 0 <= sel < 256 -> 0 <= len <= fi_n cF ->
  (forall ms, op1_call Sp ops F fc gp tp m sel wa1 wa2 wa3 wa4 cF len ms -> Q ms) ->
  evt rsegs Q (MS (mkR rr (Z_to_bv 64 Sp) gp tp x5 x6 e2 r8 (Z_to_bv 64 7) (Z_to_bv 64 sel) wa1 wa2 wa3 wa4 x15 x16
                 (Z_to_bv 64 len)
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off cF)) w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22
                 (Z_to_bv 64 (fi_n cF)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
            F (Z_to_bv 64 0x141cc) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x5 x6 e2 r8 wa1 wa2 wa3 wa4 x15 x16 w20 w22 e3 e4 e5 e6 cF sel len Q HM HC Hsel Hlen HK.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN
                  & HJ1 & HJ2 & HRW).
  unfold llvm_cursor in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  (* the three indices, as the code computes them, are the C ones (checked over every byte) *)
  set (di := Z.land (Z.shiftr sel 5) 3).
  set (dj := Z.land (Z.shiftr sel 3) 3).
  set (dk := Z.land sel 7 mod 7).
  assert (Ei : Z.land (Z.shiftr sel 3) 12 = 4 * di).
  { unfold di. apply Z.eqb_eq.
    exact (op1_byte_all (fun x => Z.land (Z.shiftr x 3) 12 =? 4 * Z.land (Z.shiftr x 5) 3)
             ltac:(vm_compute; reflexivity) sel Hsel). }
  assert (Ej : Z.land (Z.shiftr sel 1) 12 = 4 * dj).
  { unfold dj. apply Z.eqb_eq.
    exact (op1_byte_all (fun x => Z.land (Z.shiftr x 1) 12 =? 4 * Z.land (Z.shiftr x 3) 3)
             ltac:(vm_compute; reflexivity) sel Hsel). }
  assert (Ek : Z.land ((Z.b2z ((Z.land sel 7 + -7) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                 (Z.land sel 7) = dk).
  { unfold dk. apply Z.eqb_eq.
    exact (op1_byte_all (fun x => Z.land ((Z.b2z ((Z.land x 7 + -7) mod 18446744073709551616 <? 1) + -1)
                                            mod 18446744073709551616) (Z.land x 7) =? Z.land x 7 mod 7)
             ltac:(vm_compute; reflexivity) sel Hsel). }
  assert (Hdi : 0 <= di < 4).
  { unfold di. pose proof (op1_byte_all (fun x => (0 <=? Z.land (Z.shiftr x 5) 3) && (Z.land (Z.shiftr x 5) 3 <? 4))
      ltac:(vm_compute; reflexivity) sel Hsel) as P. apply andb_true_iff in P as [P1 P2]. lia. }
  assert (Hdj : 0 <= dj < 4).
  { unfold dj. pose proof (op1_byte_all (fun x => (0 <=? Z.land (Z.shiftr x 3) 3) && (Z.land (Z.shiftr x 3) 3 <? 4))
      ltac:(vm_compute; reflexivity) sel Hsel) as P. apply andb_true_iff in P as [P1 P2]. lia. }
  assert (Hdk : 0 <= dk < 7) by (unfold dk; apply Z.mod_pos_bound; lia).
  (* the table bytes *)
  assert (HR1 : ov_read_bytes rsegs m (Z_to_bv 64 (66744 + 4 * di)) 4 =
                Some (le4 (Z_to_bv 64 (nth (Z.to_nat di) [-56; -44; 16; -56] 0)))).
  { assert (C : di = 0 \/ di = 1 \/ di = 2 \/ di = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C;
      (apply op1_rom; [exact HMI | vm_compute; reflexivity | reflexivity | lia | lia]). }
  assert (HR2 : ov_read_bytes rsegs m (Z_to_bv 64 (66716 + 4 * dj)) 4 =
                Some (le4 (Z_to_bv 64 (nth (Z.to_nat dj) [-22; 16; -28; 22] 0)))).
  { assert (C : dj = 0 \/ dj = 1 \/ dj = 2 \/ dj = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C;
      (apply op1_rom; [exact HMI | vm_compute; reflexivity | reflexivity | lia | lia]). }
  assert (HR3 : ov_read_bytes rsegs m (Z_to_bv 64 (66709 + dk)) 1 =
                Some [Z_to_bv 8 (nth (Z.to_nat dk) op_frame_CMD 0)]).
  { assert (C : dk = 0 \/ dk = 1 \/ dk = 2 \/ dk = 3 \/ dk = 4 \/ dk = 5 \/ dk = 6) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; rewrite C;
      (apply op1_rom; [exact HMI | vm_compute; reflexivity | reflexivity | lia | lia]). }
  (* 0x141cc or a2, a2, a1 (send); 0x141d0-0x14210 the three table addresses *)
  do 18 zstep.
  rewrite Ei, Ej, Ek.
  (* 0x14214 lw a1 (DST[]); 0x14218 add a5; 0x1421c lw t0 (SRC[]); 0x14220 lbu a5 (CMD[]); 0x14224 add a0 (dst);
     0x14228 add s0, s3, a7 (the cursor after the take); 0x1422c sub s6, s7, a7; 0x14230 add a1 (src);
     0x14234 mv a6, s3 (the body); 0x14238 jal build_and_receive *)
  do 10 zstep.
  unfold FUZZ_INPUT_MAX in HC.
  rewrite (Z.mod_small (fi_n cF) 18446744073709551616), (Z.mod_small len 18446744073709551616) by lia.
  apply evt_done. apply HK. unfold op1_call.
  do 13 eexists. split; [reflexivity|].
  split; [|split].
  - unfold op1_dstp. fold di.
    assert (C : di = 0 \/ di = 1 \/ di = 2 \/ di = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C; vm_compute; reflexivity.
  - unfold op1_srcp. fold dj.
    assert (C : dj = 0 \/ dj = 1 \/ dj = 2 \/ dj = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C; vm_compute; reflexivity.
  - unfold op1_cmd. fold dk.
    assert (C : dk = 0 \/ dk = 1 \/ dk = 2 \/ dk = 3 \/ dk = 4 \/ dk = 5 \/ dk = 6) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; rewrite C; vm_compute; reflexivity.
Qed.

(* 0x14188-0x141c8: w = hi << 8 | lo, the take's want w % 1485 (a multiply by 0x610f, the constant the loop
   entry keeps at sp + 0x18), and the take's n = min(want, n) (0x141c4 bltu) *)
Lemma llvm_op1_t2 : forall Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x6 e2 r8 wa1 wa2 wa3 wa4 x15 x16 w20 w22 e3 e4 e5 e6 cF sel whi wlo (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D cF -> 0 <= sel < 256 -> 0 <= whi < 256 -> 0 <= wlo < 256 ->
  (forall ms, op1_call Sp ops F fc gp tp m sel wa1 wa2 wa3 wa4 cF
                (Z.min ((Z.lor (Z.shiftl whi 8) wlo) mod 1485) (fi_n cF)) ms -> Q ms) ->
  evt rsegs Q (MS (mkR rr (Z_to_bv 64 Sp) gp tp (Z_to_bv 64 whi) x6 e2 r8 (Z_to_bv 64 7) (Z_to_bv 64 sel)
                 wa1 wa2 wa3 wa4 x15 x16 (Z_to_bv 64 wlo)
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off cF)) w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22
                 (Z_to_bv 64 (fi_n cF)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
            F (Z_to_bv 64 0x14188) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x6 e2 r8 wa1 wa2 wa3 wa4 x15 x16 w20 w22 e3 e4 e5 e6 cF sel whi wlo Q HM HC Hsel Hhi Hlo HK.
  pose proof HM as HM0. pose proof HC as HC0. unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN
                  & HJ1 & HJ2 & HRW).
  unfold llvm_cursor in HC. unfold FUZZ_INPUT_MAX in HC.
  unfold LLVM_LOOP_K, LLVM_FRAME in *.
  unfold llvm_frame_consts, llvm_saved in HRW. cbn [app] in HRW.
  (* 0x14188 slli t0, t0, 8; 0x1418c or a5, t0, a7 (w); 0x14190 ld a6, 0x18(sp) (0x610f); 0x14194-0x141b8
     a5 = w - (((w - q) >> 1) + q) >> 10) * 1485 with q = (w * 0x610f) >> 16; 0x141bc ld a6, 0x20(sp) (0xffff);
     0x141c0 and a7, a5, a6; 0x141c4 bltu a7, s7 *)
  do 16 zstep.
  set (w := Z.lor (Z.shiftl whi 8) wlo).
  change (Z.lor (Z.shiftl whi 8) wlo) with w in HK.
  assert (Hw : 0 <= w < 65536).
  { unfold w. pose proof (op1_pair_all (fun h l => (0 <=? Z.lor (Z.shiftl h 8) l) && (Z.lor (Z.shiftl h 8) l <? 65536))
      ltac:(vm_compute; reflexivity) whi wlo Hhi Hlo) as P. apply andb_true_iff in P as [P1 P2]. lia. }
  (* the compiler's remainder is w mod 1485 (SPEC_MAX_BODY + 1), checked over every pair of bytes *)
  lazymatch goal with |- context [bv_ltu (Z_to_bv 64 ?e) _] =>
    assert (EW : e = w mod 1485);
    [ unfold w; apply Z.eqb_eq;
      lazymatch goal with |- ?bexp = true =>
        let P := eval pattern whi, wlo in bexp in
        lazymatch P with ?f whi wlo =>
          exact (op1_pair_all f ltac:(vm_compute; reflexivity) whi wlo Hhi Hlo) end end
    | rewrite EW ] end.
  assert (Hwm : 0 <= w mod 1485 < 1485) by (apply Z.mod_pos_bound; lia).
  if_cases K; zify_cond K.
  - (* want < n: the take's n is want (0x141cc) *)
    replace (Z.min (w mod 1485) (fi_n cF)) with (w mod 1485) in HK by lia.
    eapply llvm_op1_t3; [exact HM0 | exact HC0 | exact Hsel | lia | exact HK].
  - (* n <= want: 0x141c8 mv a7, s7 *)
    zstep.
    replace (Z.min (w mod 1485) (fi_n cF)) with (fi_n cF) in HK by lia.
    eapply llvm_op1_t3; [exact HM0 | exact HC0 | exact Hsel | lia | exact HK].
Qed.

(* 0x1417c-0x14184: fuzz_transport.c:1042-1043 `if (sel & 0x80) ack = g_last_counter;`: the code tests bit 7 by
   the sign of sel << 56 (0x1417c slli, 0x14180 bltz) and keeps a3 = g_last_counter (loaded on every path);
   else a3 = hi << 8 | lo (0x14184 or a3, a6, a5) *)
Lemma llvm_op1_t1 : forall Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x6 e2 r8 wa1 wa2 wa3 wa4 wa5 wa6 w20 w22 e3 e4 e5 e6 cF sel whi wlo (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D cF -> 0 <= sel < 256 -> 0 <= whi < 256 -> 0 <= wlo < 256 ->
  (forall ms, op1_call Sp ops F fc gp tp m sel wa1 wa2
                (if Z.land sel 128 =? 0 then Z_to_bv 64 (Z.lor (bv_unsigned wa6) (bv_unsigned wa5)) else wa3)
                wa4 cF (Z.min ((Z.lor (Z.shiftl whi 8) wlo) mod 1485) (fi_n cF)) ms -> Q ms) ->
  evt rsegs Q (MS (mkR rr (Z_to_bv 64 Sp) gp tp (Z_to_bv 64 whi) x6 e2 r8 (Z_to_bv 64 7) (Z_to_bv 64 sel)
                 wa1 wa2 wa3 wa4 wa5 wa6 (Z_to_bv 64 wlo)
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off cF)) w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22
                 (Z_to_bv 64 (fi_n cF)) (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
            F (Z_to_bv 64 0x1417c) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp x6 e2 r8 wa1 wa2 wa3 wa4 wa5 wa6 w20 w22 e3 e4 e5 e6 cF sel whi wlo Q HM HC Hsel Hhi Hlo HK.
  (* the sign of sel << 56 is bit 7 of sel (checked over every byte) *)
  assert (EB : (9223372036854775808 <=? Z.shiftl sel 56 mod 18446744073709551616) = negb (Z.land sel 128 =? 0)).
  { pose proof (op1_byte_all (fun x => Bool.eqb (9223372036854775808 <=? Z.shiftl x 56 mod 18446744073709551616)
                                                (negb (Z.land x 128 =? 0)))
      ltac:(vm_compute; reflexivity) sel Hsel) as P.
    apply Bool.eqb_prop in P. exact P. }
  (* 0x1417c slli t1, a0, 0x38; 0x14180 bltz t1 *)
  do 2 zstep.
  if_cases K; zify_cond K.
  - (* bit 7 set: ack = g_last_counter, a3 as loaded *)
    assert (E1 : (Z.land sel 128 =? 0) = false).
    { apply Z.leb_le in K. rewrite K in EB. destruct (Z.land sel 128 =? 0); [discriminate | reflexivity]. }
    rewrite E1 in HK.
    eapply llvm_op1_t2; [exact HM | exact HC | exact Hsel | exact Hhi | exact Hlo | exact HK].
  - (* bit 7 clear: 0x14184 or a3, a6, a5 *)
    assert (E1 : (Z.land sel 128 =? 0) = true).
    { apply Z.leb_gt in K. rewrite K in EB. destruct (Z.land sel 128 =? 0); [reflexivity | discriminate]. }
    rewrite E1 in HK.
    zstep.
    eapply llvm_op1_t2; [exact HM | exact HC | exact Hsel | exact Hhi | exact Hlo | exact HK].
Qed.

(* The call state with op_frame's values: sel = op1_g 0, send = g1 | g2 << 8 (a2 | a1), ack0 = g3 | g4 << 8
   (a6 | a5), g_last_counter in a3 (lw 8(s9) = OFF_g_last_counter), retry = g5 & 3, w = g6 | g7 << 8. *)
Definition op1_at (Sp ops : Z) (cA : fuzz_in) (Bw : list byte) (F : bvmap 5 word) (fc : bv 32) (gp tp : word)
    (m : word -> option byte) (ms : machine_state) : Prop :=
  exists (wa1 wa2 wa3 wa4 wa5 wa6 : word),
    op1_call Sp ops F fc gp tp m (op1_g D cA 0) wa1 wa2
      (if Z.land (op1_g D cA 0) 128 =? 0 then Z_to_bv 64 (Z.lor (bv_unsigned wa6) (bv_unsigned wa5)) else wa3)
      wa4 (op1_adv cA 8) (op1_len D cA) ms /\
    Z.lor (bv_unsigned wa2) (bv_unsigned wa1) = Z.lor (op1_g D cA 1) (Z.shiftl (op1_g D cA 2) 8) /\
    Z.lor (bv_unsigned wa6) (bv_unsigned wa5) = Z.lor (op1_g D cA 3) (Z.shiftl (op1_g D cA 4) 8) /\
    bv_unsigned wa3 mod 2 ^ 32 = g_last_counter Bw /\
    wa4 = Z_to_bv 64 (Z.land (op1_g D cA 5) 3).

(* g_last_counter as the code loads it: lw 8(s9) = OFF_g_last_counter (0xfdd0 = 64976), sign-extended *)
Lemma op1_lastc : forall Bw, bv_unsigned (Z_to_bv 64 (s32_at Bw 64976)) mod 2 ^ 32 = g_last_counter Bw.
Proof.
  intros Bw. rewrite unsigned_lit_wrap.
  set (s := s32_at Bw 64976).
  replace (s mod 2 ^ 64) with (s + (- (s / 2 ^ 64) * 2 ^ 32) * 2 ^ 32)
    by (rewrite Z.mod_eq by lia; ring).
  rewrite Z.mod_add by lia. unfold s.
  unfold g_last_counter, s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change OFF_g_last_counter with 64976.
  pose proof (u_at_range Bw 64976 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  rewrite Zminus_mod_idemp_l. replace (u_at Bw 64976 4 + 2 ^ 31 - 2 ^ 31) with (u_at Bw 64976 4) by lia.
  apply Z.mod_small. exact R.
Qed.

(* 0x1417c on, with the registers the paths leave and their values as op_frame's *)
Lemma llvm_op1_t0 : forall Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp wt0 x6 e2 r8 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w19 w20 w22 w23 e3 e4 e5 e6 cA
    (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  llvm_cursor D cA ->
  wa0 = Z_to_bv 64 (op1_g D cA 0) -> wa1 = Z_to_bv 64 (op1_g D cA 1) ->
  wa2 = Z_to_bv 64 (Z.shiftl (op1_g D cA 2) 8) -> wa3 = Z_to_bv 64 (s32_at Bw 64976) ->
  wa4 = Z_to_bv 64 (Z.land (op1_g D cA 5) 3) -> wa5 = Z_to_bv 64 (op1_g D cA 3) ->
  bv_unsigned wa6 = Z.shiftl (op1_g D cA 4) 8 -> wa7 = Z_to_bv 64 (op1_g D cA 6) ->
  wt0 = Z_to_bv 64 (op1_g D cA 7) ->
  w19 = Z_to_bv 64 (data + fi_off (op1_adv cA 8)) -> w23 = Z_to_bv 64 (fi_n (op1_adv cA 8)) ->
  (forall ms, op1_at Sp ops cA Bw F fc gp tp m ms -> Q ms) ->
  evt rsegs Q (MS (mkR rr (Z_to_bv 64 Sp) gp tp wt0 x6 e2 r8 (Z_to_bv 64 7) wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7
                 (Z_to_bv 64 0x39) w19 w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22 w23
                 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
            F (Z_to_bv 64 0x1417c) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp wt0 x6 e2 r8 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w19 w20 w22 w23 e3 e4 e5 e6 cA Q
    HM HC E0 E1 E2 E3 E4 E5 E6 E7 E8 E19 E23 HK.
  subst wa0 wa1 wa2 wa3 wa4 wa5 wa7 wt0 w19 w23.
  pose proof (op1_g_range D cA 1) as R1. pose proof (op1_g_range D cA 2) as R2.
  pose proof (op1_g_range D cA 3) as R3. pose proof (op1_g_range D cA 4) as R4.
  pose proof (op1_g_range D cA 6) as R6. pose proof (op1_g_range D cA 7) as R7.
  assert (S2 : 0 <= Z.shiftl (op1_g D cA 2) 8 < 65536) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (HC8 : llvm_cursor D (op1_adv cA 8)) by (unfold llvm_cursor, op1_adv in *; cbn [fi_off fi_n]; lia).
  eapply llvm_op1_t1; [exact HM | exact HC8 | apply op1_g_range | apply op1_g_range | apply op1_g_range |].
  intros ms Hms. apply HK. exists (Z_to_bv 64 (op1_g D cA 1)), (Z_to_bv 64 (Z.shiftl (op1_g D cA 2) 8)),
    (Z_to_bv 64 (s32_at Bw 64976)), (Z_to_bv 64 (Z.land (op1_g D cA 5) 3)), (Z_to_bv 64 (op1_g D cA 3)), wa6.
  replace (Z.min (Z.lor (Z.shiftl (op1_g D cA 7) 8) (op1_g D cA 6) mod 1485) (fi_n (op1_adv cA 8)))
    with (op1_len D cA) in Hms.
  2: { unfold op1_len.
       rewrite (Z.mod_small (Z.lor (op1_g D cA 6) (Z.shiftl (op1_g D cA 7) 8)) (2 ^ 16))
         by (rewrite lor_shiftl8_add by lia; lia).
       rewrite (Z.lor_comm (op1_g D cA 6)). reflexivity. }
  split; [exact Hms|].
  split; [rewrite !unsigned_lit by lia; apply Z.lor_comm|].
  split; [rewrite E6, unsigned_lit by lia; apply Z.lor_comm|].
  split; [apply op1_lastc | reflexivity].
Qed.

(* 0x142b0 slliw a6, a4, 8 on a byte: the 32-bit shift stays positive *)
Lemma op1_sw8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned b) 8))) = Z.shiftl (bv_unsigned b) 8.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by lia. apply unsigned_lit. lia.
Qed.

(* a register the paths leave, against op_frame's value: decide each op1_g by the path's cursor length, then
   peel the two sides down to the first arithmetic difference *)
Ltac op1_feq := first [ reflexivity | lia | (f_equal; op1_feq) ].
Ltac op1_reg :=
  rewrite ?op1_sw8;
  unfold op1_g, op1_adv; cbn [fi_off fi_n];
  repeat match goal with
  | |- context [?j <? ?n] =>
      first [ rewrite (proj2 (Z.ltb_lt j n)) by lia | rewrite (proj2 (Z.ltb_ge j n)) by lia ]
  end;
  op1_feq.

(* 0x139ec-0x1417c (the op byte already read): op_frame's 8 reads (fuzz_transport.c:1040-1045), as the code
   unrolls them per cursor length: s4 / s7 the cursor before the op byte, byte j at s4 + j, each read only when
   s7 > j; the reads that miss are 0. *)
Lemma llvm_op1_walk : forall Sp lo ops c cA Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 t3 t4 t5 t6 (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  fi_n c <> 0 -> llvm_cursor D c -> cA = fst (fuzz_u8_m D c) ->
  (forall ms, op1_at Sp ops cA Bw F fc gp tp m ms -> Q ms) ->
  evt rsegs Q (MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off cA)) (Z_to_bv 64 (data + fi_off c))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n cA)) (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x139ec) fc None m (seg_rom rsegs)).
Proof.
  intros Sp lo ops c cA Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m j10 j28
    rr gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 t3 t4 t5 t6 Q HM HN HC HCA HK.
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN
                  & HJ1 & HJ2 & HRW).
  pose proof (wm_len _ _ _ _ HWM) as LB.
  wk_facts. wk_eq_fact OFF_g_fail_next.
  assert (HCA' : llvm_cursor D (FuzzIn (fi_off c + 1) (fi_n c - 1))) by (unfold llvm_cursor in *; cbn; lia).
  unfold llvm_cursor, FUZZ_INPUT_MAX in HC.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (EA : cA = FuzzIn (fi_off c + 1) (fi_n c - 1)).
  { rewrite HCA. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  clear HCA. subst cA. cbn [fi_off fi_n].
  (* the input byte j places after the op byte's position, when the cursor holds it *)
  assert (HRB : forall j, 0 <= j < fi_n c ->
            ov_read_bytes rsegs m (wa (data + (fi_off c + j))) 1 = Some [nth (Z.to_nat (fi_off c + j)) D (b8 0)]).
  { intros j Hj. pose proof (bytes_at_read rsegs m data D (fi_off c + j) 1 HD ltac:(lia) ltac:(lia)) as HR.
    rewrite disp_sub1 in HR by lia. exact HR. }
  (* 0x139ec beqz s6: no byte after the op byte *)
  zstep.
  if_cases K; zify_cond K.
  { (* 0x13b4c-0x13b5c a2 = a1 = a0 = a5 = 0, j 0x14164; 0x14164-0x14178 a6 = s7 = a4 = a7 = 0,
       lw a3, 8(s9) (g_last_counter), t0 = 0 *)
    try (rewrite Z.mod_small in K by lia).
    do 11 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x139f0 lbu a0, 1(s4) (sel); 0x139f4 li a1, 2; 0x139f8 bne s7, a1 *)
  try (rewrite Z.mod_small in K by lia).
  pose proof (HRB 1 ltac:(lia)) as HR1.
  do 3 zstep.
  if_cases K2; zify_cond K2.
  2: { (* n = 2: 0x139fc-0x13a0c a2 = a1 = a5 = 0, s3 = s4 + 2, j 0x14164; then as above *)
    try (rewrite Z.mod_small in K2 by lia).
    do 11 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x13c88 lbu a1, 2(s4) (send lo); 0x13c8c li a2, 3; 0x13c90 bne s7, a2 *)
  try (rewrite Z.mod_small in K2 by lia).
  pose proof (HRB 2 ltac:(lia)) as HR2.
  do 3 zstep.
  if_cases K3; zify_cond K3.
  2: { (* n = 3: 0x13c94-0x13ca0 a2 = a5 = 0, s3 = s4 + 3, j 0x14164 *)
    try (rewrite Z.mod_small in K3 by lia).
    do 10 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x13f0c lbu a2, 3(s4); 0x13f10 slli a2, a2, 8 (send hi); 0x13f14 li a3, 4; 0x13f18 bne s7, a3 *)
  try (rewrite Z.mod_small in K3 by lia).
  pose proof (HRB 3 ltac:(lia)) as HR3.
  do 4 zstep.
  if_cases K4; zify_cond K4.
  2: { (* n = 4: 0x13f1c-0x13f24 a5 = 0, s3 = s4 + 4, j 0x14164 *)
    try (rewrite Z.mod_small in K4 by lia).
    do 9 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x14154 lbu a5, 4(s4) (ack lo); 0x14158 li a3, 5; 0x1415c bne s7, a3 *)
  try (rewrite Z.mod_small in K4 by lia).
  pose proof (HRB 4 ltac:(lia)) as HR4.
  do 3 zstep.
  if_cases K5; zify_cond K5.
  2: { (* n = 5: 0x14160 s3 = s4 + 5, on into 0x14164 *)
    try (rewrite Z.mod_small in K5 by lia).
    do 7 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x142a8 lbu a4, 5(s4) (ack hi); 0x142ac lw a3, 8(s9) (g_last_counter); 0x142b0 slliw a6, a4, 8;
     0x142b4 li a4, 6; 0x142b8 bne s7, a4 *)
  try (rewrite Z.mod_small in K5 by lia).
  pose proof (HRB 5 ltac:(lia)) as HR5.
  do 5 zstep.
  if_cases K6; zify_cond K6.
  2: { (* n = 6: 0x142bc-0x142d0 s7 = a4 = a7 = t0 = 0, s3 = s4 + 6, j 0x1417c *)
    try (rewrite Z.mod_small in K6 by lia).
    do 6 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x142d4 lbu a4, 6(s4) (r); 0x142d8 andi a4, a4, 3 (retry); 0x142dc bne s7, s1 (s1 = 7) *)
  try (rewrite Z.mod_small in K6 by lia).
  pose proof (HRB 6 ltac:(lia)) as HR6.
  do 3 zstep.
  if_cases K7; zify_cond K7.
  2: { (* n = 7: 0x142e0-0x142f0 s7 = a7 = t0 = 0, s3 = s4 + 7, j 0x1417c *)
    try (rewrite Z.mod_small in K7 by lia).
    do 5 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* 0x142f4 lbu a7, 7(s4) (w lo); 0x142f8 li t0, 8; 0x142fc bne s7, t0 *)
  try (rewrite Z.mod_small in K7 by lia).
  pose proof (HRB 7 ltac:(lia)) as HR7.
  do 3 zstep.
  if_cases K8; zify_cond K8.
  2: { (* n = 8: 0x14300-0x1430c s7 = t0 = 0, s3 = s4 + 8, j 0x1417c *)
    try (rewrite Z.mod_small in K8 by lia).
    do 4 zstep.
    eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK]. }
  (* n > 8: 0x14310 lbu t0, 8(s4) (w hi); 0x14314 s7 -= 9; 0x14318 s3 = s4 + 9; 0x1431c j 0x1417c *)
  try (rewrite Z.mod_small in K8 by lia).
  pose proof (HRB 8 ltac:(lia)) as HR8.
  do 4 zstep.
  eapply llvm_op1_t0; [exact HM0 | exact HCA' | op1_reg .. | exact HK].
Qed.

(* 0x1423c-0x14288 after build_and_receive returns: j 0x14288; mv s3, s0 (the cursor after the take); the latch *)
Lemma llvm_op1_post : forall tp Sp lo ops c6 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m j10 j28
    x1 gp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31 (Q : machine_state -> Prop),
  llvm_mem data D Sp lo Bw m m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  0 <= ops < OPS_MAX -> llvm_cursor D c6 ->
  x8 = Z_to_bv 64 (data + fi_off c6) -> x22 = Z_to_bv 64 (fi_n c6) ->
  (forall ms, llvm_latch data D m gp tp Sp lo ops c6 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms -> Q ms) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 (Z_to_bv 64 7)
                   x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x39) x19 x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
                   x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                   (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) x28 x29 x30 x31)
            F (Z_to_bv 64 0x1423c) fc None m (seg_rom rsegs)).
Proof.
  intros tp Sp lo ops c6 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m j10 j28
    x1 gp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31 Q HM HOPS HC E8 E22 HK.
  subst x8 x22.
  (* 0x1423c j 0x14288; 0x14288 mv s3, s0 *)
  do 2 zstep.
  apply evt_done. apply HK. unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC | exact HM].
Qed.

End OP1.

(* ---- the pieces the SR step needs ---- *)

Lemma op1_ms_inv : forall R F pc fc rv m ro R' F' pc' fc' rv' m' ro',
  MS R F pc fc rv m ro = MS R' F' pc' fc' rv' m' ro' -> R = R' /\ F = F' /\ pc = pc' /\ fc = fc' /\ m = m'.
Proof.
  intros R F pc fc rv m ro R' F' pc' fc' rv' m' ro' H. unfold MS in H. inversion H.
  repeat split; reflexivity.
Qed.

(* TOps.v LLVMFuzzerTestOneInput_op_m at op 1 *)
Lemma op1_model : forall I B A D c k, snd (fuzz_u8_m D c) mod 9 = 1 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k =
    match op_frame_m I B D (A k) (fst (fuzz_u8_m D c)) with
    | Some (B1, c2) => Some (B1, (c2, S k))
    | None => None
    end.
Proof.
  intros I B A D c k H. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in *. rewrite H. reflexivity.
Qed.

Lemma op1_land3 : forall x, 0 <= Z.land x 3 < 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* the MAC tables of op_frame, at the pointers the code computes (checked against the image) *)
Lemma op1_dst_mac : forall sel,
  length (nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) op_frame_DST []) = 6%nat /\
  LLVMFuzzerTestOneInput_sr.mac_rom_ok (op1_dstp sel) (nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) op_frame_DST []) = true /\
  0 <= op1_dstp sel < 2 ^ 64.
Proof.
  intros sel. unfold op1_dstp. pose proof (op1_land3 (Z.shiftr sel 5)) as R.
  assert (C : Z.land (Z.shiftr sel 5) 3 = 0 \/ Z.land (Z.shiftr sel 5) 3 = 1 \/
              Z.land (Z.shiftr sel 5) 3 = 2 \/ Z.land (Z.shiftr sel 5) 3 = 3) by lia.
  destruct C as [C|[C|[C|C]]]; rewrite C;
    (split; [reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
Qed.

Lemma op1_src_mac : forall sel,
  length (nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) op_frame_SRC []) = 6%nat /\
  LLVMFuzzerTestOneInput_sr.mac_rom_ok (op1_srcp sel) (nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) op_frame_SRC []) = true /\
  0 <= op1_srcp sel < 2 ^ 64.
Proof.
  intros sel. unfold op1_srcp. pose proof (op1_land3 (Z.shiftr sel 3)) as R.
  assert (C : Z.land (Z.shiftr sel 3) 3 = 0 \/ Z.land (Z.shiftr sel 3) 3 = 1 \/
              Z.land (Z.shiftr sel 3) 3 = 2 \/ Z.land (Z.shiftr sel 3) 3 = 3) by lia.
  destruct C as [C|[C|[C|C]]]; rewrite C;
    (split; [reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
Qed.

Lemma op1_cmd_range : forall sel, 0 <= op1_cmd sel < 2 ^ 8.
Proof.
  intros sel. unfold op1_cmd. pose proof (Z.mod_pos_bound (Z.land sel 7) 7 ltac:(lia)) as R.
  assert (C : Z.land sel 7 mod 7 = 0 \/ Z.land sel 7 mod 7 = 1 \/ Z.land sel 7 mod 7 = 2 \/
              Z.land sel 7 mod 7 = 3 \/ Z.land sel 7 mod 7 = 4 \/ Z.land sel 7 mod 7 = 5 \/
              Z.land sel 7 mod 7 = 6) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; rewrite C;
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
Qed.

Lemma op1_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n H Hk Hn. unfold sub.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Z.of_nat (Nat.min (Z.to_nat k) (length bs))) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Section OP1SR.
Context {rc : YM05.RunCeil}.
Variable B : YO0d.malloc_syms.
Variable API : YO0d.AllocAPI B.
Context (data : Z) (D : list byte).

(* Case 1 as an SR step of the loop: from the SR config at its entry (0x139ec), with the model's op at every heap
   frame address a successful malloc can return (the stream A with index k set to a, TOpsA.v aupd), to the SR
   config at the latch with the world and the cursor the model's op gives at the a build_and_receive's malloc
   returned. The callee contract is taken at every FP state. *)
Lemma llvm_op1_sr : forall gp tp Sp lo ops c c1 Bw (A : nat -> Z) (k : nat) L0 A0 mem0 md0 b
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cfg (P : config -> Prop),
  receive_c.h_binds B API ->
  (forall fx'' : YK11.FPState, @build_and_receive_c.build_and_receive_contract fx'' rc B API) ->
  snd (fuzz_u8_m D c) mod 9 = 1 ->
  LLVMFuzzerTestOneInput_sr.llvm_case_sr B API data D gp tp 1 Sp lo ops c c1 Bw
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall a, receive_c.h_addr_ok a -> exists Bres cout k1,
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, k1))) ->
  (forall a Bres cout cfg', receive_c.h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, S k)) ->
     LLVMFuzzerTestOneInput_sr.llvm_latch_sr B API data D gp tp Sp lo ops cout Bres
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' ->
     YM06.SR rsegs cfg' P) ->
  YM06.SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c c1 Bw A k L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cfg P
    HB HBAR Hop HCASE HMOD HK.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  destruct HCASE as (fx & regs & mem & md & L & A1 & -> & Hfrm & FR & Hceil & Hlo & Hres & Hroom & Htp & HIN & HC).
  cbv beta in HC.
  destruct HC as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & mm &
                  j10 & j28 & EMS & HOPS & HN & HCc & HC1 & HM).
  destruct (op1_ms_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as (ER0 & _ & _ & _ & EM). subst mm.
  assert (Etp : tp = Z_to_bv 64 (YO0d.ms_tp B)).
  { rewrite <- Htp. change (YK11.getr regs 4) with (reg_get (Regs6ss.mkR_of regs) 4). rewrite ER0. reflexivity. }
  pose proof HM as HMc. unfold llvm_mem in HMc.
  destruct HMc as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2
                   & HRW).
  pose proof HCc as HCc'. unfold llvm_cursor in HCc'. unfold FUZZ_INPUT_MAX in HCc'.
  assert (EC1 : c1 = FuzzIn (fi_off c + 1) (fi_n c - 1)).
  { rewrite HC1. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  assert (HN1 : 0 <= fi_n c1) by (rewrite EC1; cbn; lia).
  set (sel := op1_g D c1 0).
  set (cF := op1_adv c1 8).
  set (len := op1_len D c1).
  assert (Hlen : 0 <= len <= fi_n cF).
  { unfold len, op1_len. fold cF. pose proof (Z.mod_pos_bound (Z.lor (op1_g D c1 6) (Z.shiftl (op1_g D c1 7) 8) mod 2 ^ 16) 1485 ltac:(lia)).
    unfold cF, op1_adv. cbn [fi_n]. lia. }
  assert (HCF : 0 <= fi_off cF /\ fi_off cF + fi_n cF <= Z.of_nat (length D)).
  { unfold cF, op1_adv. rewrite EC1. cbn [fi_off fi_n]. lia. }
  unfold LLVM_FRAME in HSP2.
  assert (HSPm : LLVMFuzzerTestOneInput_sr.LLVM_SR_S Sp <= 2 ^ 64)
    by (unfold LLVMFuzzerTestOneInput_sr.LLVM_SR_S, LLVM_FRAME; lia).
  (* ---- 0x139ec-0x14238: the evt walk to the call ---- *)
  eapply (TSRGlue.g_run B API SEGS AX HGG WORLD LLVMFuzzerTestOneInput_sr.LLVM_SR_K
            (LLVMFuzzerTestOneInput_sr.LLVM_SR_S Sp) L0 A0 mem0 md0 fx regs (Z_to_bv 64 (LLVM_CASE 1)) mem md L A1
            (op1_at data D Sp ops c1 Bw (@YK11.fp_regs fx) (@YK11.fp_csr fx) gp tp (MemNorm.normalize rsegs mem))
            P FR Hceil HSPm).
  { rewrite ER0. unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
    eapply (llvm_op1_walk data D); [exact HM | exact HN | exact HCc | exact HC1 | intros ms Hms; exact Hms]. }
  { intros ms HQ. destruct HQ as (wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & HCALL & _).
    destruct HCALL as (u0 & u1 & u2 & w19 & w20 & w23 & u3 & u4 & u5 & u6 & dstp & srcp & cmd & -> & _).
    eexists _, _, _, _, _, []. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x _ Hno. exfalso. apply Hno. exact I. }
  intros R F' pc' fc' m0' HQ regs' m' Hx Hrel FR'.
  destruct HQ as (wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & HCALL & ES & EA & EL & ER).
  destruct HCALL as (u0 & u1 & u2 & w19 & w20 & w23 & u3 & u4 & u5 & u6 & dstp & srcp & cmd & EMS2 & Edst & Esrc & Ecmd).
  destruct (op1_ms_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS2) as (-> & -> & -> & -> & ->).
  pose proof FR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI' & _).
  (* the loop's invariant restarted over the memory of the SR config *)
  assert (HM' : llvm_mem data D Sp lo Bw (MemNorm.normalize rsegs m') (MemNorm.normalize rsegs m')
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { apply (LLVMFuzzerTestOneInput_sr.llvm_mem_ext data D Sp lo Bw (MemNorm.normalize rsegs mem)
             (MemNorm.normalize rsegs mem)); [| exact HM].
    intros x. destruct Hrel as [E _]. symmetry. apply E. }
  (* the registers at the call *)
  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x1423c) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2 : YK11.getr regs' 2 = Z_to_bv 64 Sp) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G4 : YK11.getr regs' 4 = Z_to_bv 64 (YO0d.ms_tp B))
    by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); rewrite <- Etp; reflexivity).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 dstp) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G11 : YK11.getr regs' 11 = Z_to_bv 64 srcp) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G12 : YK11.getr regs' 12 = Z_to_bv 64 (Z.lor (bv_unsigned wa2) (bv_unsigned wa1)))
    by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G13 : YK11.getr regs' 13 =
                (if Z.land sel 128 =? 0 then Z_to_bv 64 (Z.lor (bv_unsigned wa6) (bv_unsigned wa5)) else wa3))
    by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G14 : YK11.getr regs' 14 = wa4) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G15 : YK11.getr regs' 15 = Z_to_bv 64 cmd) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G16 : YK11.getr regs' 16 = Z_to_bv 64 (data + fi_off cF)) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G17 : YK11.getr regs' 17 = Z_to_bv 64 len) by (rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx); reflexivity).
  pose proof (op1_g_range D c1 1) as R1. pose proof (op1_g_range D c1 2) as R2.
  pose proof (op1_g_range D c1 3) as R3. pose proof (op1_g_range D c1 4) as R4.
  pose proof (op1_dst_mac sel) as (DL & DM & DR). pose proof (op1_src_mac sel) as (SL & SM & SR').
  set (body := sub D (fi_off cF) (Z.to_nat len)).
  assert (LBODY : Z.of_nat (length body) = len) by (unfold body; rewrite length_sub by lia; lia).
  (* ---- 0x15be4: build_and_receive ---- *)
  change (Z_to_bv 64 0x15be4) with (Z_to_bv 64 build_and_receive_c.build_and_receive_ENTRY).
  apply (LLVMFuzzerTestOneInput_sr.llvm_sr_bar B API data D Sp lo Bw (YK11.mkFP (@YK11.fp_regs fx) (@YK11.fp_csr fx))
           regs' (MemNorm.normalize rsegs m') m' md L A1 L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
           (op1_dstp sel) (op1_srcp sel) (data + fi_off cF)
           (nth (Z.to_nat (Z.land (Z.shiftr sel 5) 3)) op_frame_DST [])
           (nth (Z.to_nat (Z.land (Z.shiftr sel 3) 3)) op_frame_SRC []) body
           (Z.lor (op1_g D c1 1) (Z.shiftl (op1_g D c1 2) 8) mod 2 ^ 16)
           (if Z.land sel 0x80 =? 0 then Z.lor (op1_g D c1 3) (Z.shiftl (op1_g D c1 4) 8) mod 2 ^ 16
            else g_last_counter Bw)
           (Z.land (op1_g D c1 5) 3) (op1_cmd sel) P HB HBAR FR' Hlo Hfrm Hres Hroom G2 G4);
    [ rewrite G1; reflexivity | exact HM' | exact HIN | | ].
  { (* bar_args *)
    assert (S12 : 0 <= Z.lor (op1_g D c1 1) (Z.shiftl (op1_g D c1 2) 8) < 2 ^ 16)
      by (rewrite lor_shiftl8_add by lia; lia).
    assert (S34 : 0 <= Z.lor (op1_g D c1 3) (Z.shiftl (op1_g D c1 4) 8) < 2 ^ 16)
      by (rewrite lor_shiftl8_add by lia; lia).
    unfold build_and_receive_c.bar_args.
    split; [rewrite G10; apply bv_eq; rewrite !unsigned_lit_wrap, Edst; symmetry; apply Z.mod_small; exact DR|].
    split; [apply LLVMFuzzerTestOneInput_sr.llvm_mac_img; [exact SEGS | exact MI' | exact DL | exact DM]|].
    split; [rewrite G11; apply bv_eq; rewrite !unsigned_lit_wrap, Esrc; symmetry; apply Z.mod_small; exact SR'|].
    split; [apply LLVMFuzzerTestOneInput_sr.llvm_mac_img; [exact SEGS | exact MI' | exact SL | exact SM]|].
    split; [rewrite G12, ES, unsigned_lit by lia; rewrite !Z.mod_small by lia; reflexivity|].
    split; [apply Z.mod_pos_bound; lia|].
    split.
    { rewrite G13. change 0x80 with 128. destruct (Z.land sel 128 =? 0).
      - rewrite EA, unsigned_lit by lia. rewrite !Z.mod_small by lia. reflexivity.
      - exact EL. }
    split.
    { change 0x80 with 128. destruct (Z.land sel 128 =? 0); [lia|].
      unfold g_last_counter. pose proof (u_at_range Bw OFF_g_last_counter 4) as R. cbn in R. lia. }
    split; [rewrite G14; exact ER|].
    split; [pose proof (op1_land3 (op1_g D c1 5)); lia|].
    split; [rewrite G15, Ecmd; reflexivity|].
    split; [apply op1_cmd_range|].
    split; [exact G16|].
    split; [rewrite G17, LBODY; reflexivity|].
    split.
    { apply LLVMFuzzerTestOneInput_sr.llvm_blk_norm; [exact SEGS | exact MI'|].
      unfold llvm_mem in HM'. destruct HM' as (_ & _ & HD' & _).
      unfold body. apply op1_bytes_sub; [exact HD' | lia | lia]. }
    split.
    { rewrite LBODY.
      apply (LLVMFuzzerTestOneInput_sr.llvm_src_data B API data D LLVMFuzzerTestOneInput_sr.LLVM_SR_K
               (LLVMFuzzerTestOneInput_sr.LLVM_SR_S Sp) L0 A0 mem0 md0 L A1 m' md);
        [exact FR' | exact HIN | lia | lia |]. unfold off_world in HOW |- *. lia. }
    (* the model: build_and_receive_m is defined at every address malloc can return *)
    intros a Ha HNone. destruct (HMOD a Ha) as (Bres & cout & k1 & E).
    rewrite (op1_model _ _ _ _ _ _ Hop), aupd_at, <- HC1, (op1_frame_eq _ _ _ _ _ HN1) in E.
    fold sel cF len body in E. rewrite HNone in E. discriminate E. }
  (* ---- 0x1423c: back from build_and_receive ---- *)
  intros fx'' regs'' mem'' md'' L' A' a Bw' Ha HBM Hrp Hfrm2 FR2 Hres2 HM2.
  rewrite G1.
  pose proof FR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI2 & _).
  (* the model's op at A k = a *)
  assert (EOP : LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bw', (op1_c6 D c1, S k))).
  { rewrite (op1_model _ _ _ _ _ _ Hop), aupd_at, <- HC1, (op1_frame_eq _ _ _ _ _ HN1).
    fold sel cF len body. rewrite HBM. reflexivity. }
  (* the callee-saved registers, kept by the callee *)
  assert (CS : forall r, YO0d.callee_saved r ->
                 YK11.getr regs'' (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) by exact Hrp.
  assert (E2 : reg_get regs'' 2 = Z_to_bv 64 Sp).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 2)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). exact G2. }
  assert (E3 : reg_get regs'' 3 = gp).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 3)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E4 : reg_get regs'' 4 = tp).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 4)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E8 : reg_get regs'' 8 = Z_to_bv 64 (data + fi_off cF + len)).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 8)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E9 : reg_get regs'' 9 = Z_to_bv 64 7).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 9)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E18 : reg_get regs'' 18 = Z_to_bv 64 0x39).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 18)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E21 : reg_get regs'' 21 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 21)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E22 : reg_get regs'' 22 = Z_to_bv 64 (fi_n cF - len)).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 22)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E24 : reg_get regs'' 24 = Z_to_bv 64 1).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 24)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E25 : reg_get regs'' 25 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 25)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E26 : reg_get regs'' 26 = Z_to_bv 64 (W_BASE_PLAIN + OFF_M)).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 26)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (E27 : reg_get regs'' 27 = Z_to_bv 64 ops).
  { transitivity (YK11.getr regs'' (Z_to_bv 5 27)); [reflexivity|].
    rewrite CS by (unfold YO0d.callee_saved; lia). rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx). reflexivity. }
  assert (HC6 : llvm_cursor D (op1_c6 D c1)).
  { unfold llvm_cursor, op1_c6. fold cF len. cbn [fi_off fi_n]. unfold FUZZ_INPUT_MAX. lia. }
  (* ---- 0x1423c-0x14288: the evt walk to the latch ---- *)
  eapply (TSRGlue.g_run B API SEGS AX HGG WORLD LLVMFuzzerTestOneInput_sr.LLVM_SR_K
            (LLVMFuzzerTestOneInput_sr.LLVM_SR_S Sp) L0 A0 mem0 md0 fx'' regs'' (Z_to_bv 64 0x1423c) mem'' md'' L' A'
            (llvm_latch data D (MemNorm.normalize rsegs mem'') gp tp Sp lo ops (op1_c6 D c1) Bw'
               ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (@YK11.fp_regs fx'') (@YK11.fp_csr fx''))
            P FR2 Hceil HSPm).
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E18, E21, E22, E24, E25, E26, E27.
    eapply (llvm_op1_post data D); [exact HM2 | exact HOPS | exact HC6 | | | intros ms Hms; exact Hms].
    - f_equal. unfold op1_c6. fold cF len. cbn [fi_off]. lia.
    - reflexivity. }
  { intros ms HQ. destruct HQ as (rr' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & r8' & r20 & r23 &
                                 v3 & v4 & v5 & v6 & mm & j10' & j28' & -> & _ & _ & HMl).
    pose proof HMl as (HMU & HWMO & _).
    eexists _, _, _, _, mm, (LLVM_FP Sp). split; [reflexivity|]. split; [exact HMU|]. split; [exact HWMO|].
    intros x _ Hout.
    assert (Hin : (Sp - 9856 <= x < Sp + 224) \/ (W_BASE_PLAIN <= x < W_BASE_PLAIN + W_LEN)).
    { unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in Hout. cbn [outside] in Hout. lia. }
    destruct Hin as [Hin|Hin].
    - left. unfold LLVMFuzzerTestOneInput_sr.LLVM_SR_S, LLVMFuzzerTestOneInput_sr.LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME.
      lia.
    - right. left. unfold receive_c.h_world. exact Hin. }
  intros R F pc fc m0' HQ regs''' m''' Hx2 Hrel2 FR3.
  pose proof HQ as HQ0.
  destruct HQ as (rr' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & r8' & r20 & r23 &
                  v3 & v4 & v5 & v6 & mm & j10' & j28' & EMS3 & _ & _ & _).
  destruct (op1_ms_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS3) as (ER3 & EF3 & EP3 & EC3 & EM3).
  subst R F pc fc m0'.
  apply (HK a Bw' (op1_c6 D c1) _ Ha EOP).
  unfold LLVMFuzzerTestOneInput_sr.llvm_latch_sr, LLVMFuzzerTestOneInput_sr.llvm_sr_at.
  exists (YK11.mkFP (@YK11.fp_regs fx'') (@YK11.fp_csr fx'')), regs''', m''', md'', L', A'.
  split; [reflexivity|].
  split; [exact Hfrm2|].
  split; [exact FR3|].
  split; [exact Hceil|]. split; [exact Hlo|]. split; [exact Hres2|]. split; [exact Hroom|].
  split; [rewrite (TSRGlue.sr_getr_eqv _ _ _ Hx2); rewrite <- Etp; reflexivity|].
  split; [exact HIN|].
  cbv beta.
  erewrite LLVMFuzzerTestOneInput_sr.llvm_mkR_of_eqv by exact Hx2.
  apply (LLVMFuzzerTestOneInput_sr.llvm_latch_ext data D gp tp (MemNorm.normalize rsegs mem'') Sp lo ops
           (op1_c6 D c1) Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (@YK11.fp_regs fx'') (@YK11.fp_csr fx'')
           _ _ _ mm).
  - intros x. destruct Hrel2 as [E _]. symmetry. apply E.
  - exact HQ0.
Qed.

End OP1SR.
