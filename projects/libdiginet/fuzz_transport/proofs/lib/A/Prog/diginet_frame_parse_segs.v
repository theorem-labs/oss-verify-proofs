(* diginet_frame_parse_segs: the cut points of the image-A walk of diginet_frame_parse (fuzz_frame.asan 0x82080 =
   dgnframe_sigma DF_diginet_frame_parse, 0x5fc bytes), and the footprint runs (lib/Lib/ExecF.v evtF, stepped by
   lib/Lib/StepF.v) between them, as statements. lib/A/Prog/diginet_frame_parse_walk.v carries each run into SRr
   and cuts the two __asan_memcpy calls by their contract.

   The runs (offsets from the entry; the neutral listing diginet_frame_parse.fuzz_frame.asan.s):
     fp_head_stmt  +0x000 -> the first __asan_memcpy call (+0x0ec, `jal` 0x50dc0, ra = +0x0f0), or the return:
                   the 48-byte frame (s4, s3, s2, s1, s0, ra at 0(sp) .. 40(sp)), the null checks (not taken),
                   size < 30 (-2), the shadow base through GOT_CELL_K -> CELL_K, buf[12], buf[13] (EtherType,
                   -3), buf[14], buf[15] (numbytes, s4; -4), each load after the check of its shadow byte;
     fp_mid_F      +0x0f0 -> the second __asan_memcpy call (+0x0fc, ra = +0x100): a0 = s0 + 6, a1 = s1 + 6, a2 = 6;
     fp_hdr1_stmt  +0x100 -> +0x220: the stores of the EtherType (f + 12), numbytes (f + 16), the sum (f + 18,
                   buf[16..17]) and the send counter (f + 20, buf[18..21]);
     fp_hdr2_stmt  +0x220 -> +0x3b0: the ack counter (f + 24, buf[22..25]), retry (f + 28, buf[26..27]), cmd
                   (f + 30, buf[28]), num_commands (f + 31, buf[29]), body (f + 32), body_len (f + 40), pad_len
                   (f + 48); at +0x3b0 a3 = body_len, a1 = buf + 30, a2 = the sum;
     fp_tail_stmt  +0x3b0 -> the return: the body-sum loop (+0x3bc .. +0x3e0, skipped when body_len = 0), the cut
                   to 16 bits (+0x418), body_sum (f + 56), sum_matches (f + 58), a0 = 0, the epilogue.
   Every load or store of buf or f follows the check of its shadow byte at (a >> 3) + ASAN_K; the addressable
   premises make every check pass, so no errpath_* call (+0x3f0, +0x468 .. +0x5f8) is reached. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- addresses ---- *)
Definition FP_ENTRY : Z := transport_sigma TS_diginet_frame_parse.
Definition FP_AT (off : Z) : Z := FP_ENTRY + off.
Definition FP_MEMCPY : Z := transport_sigma TS___asan_memcpy.
(* the return addresses of the two __asan_memcpy calls *)
Definition FP_RET1 : Z := FP_AT 0xf0.
Definition FP_RET2 : Z := FP_AT 0x100.
(* the cut inside the stores of the header fields *)
Definition FP_HDR2 : Z := FP_AT 0x220.
(* `beqz a3` (body_len = 0) before the body-sum loop *)
Definition FP_SUMQ : Z := FP_AT 0x3b0.

Lemma FP_vals : FP_ENTRY = 0x8b6fc /\ FP_MEMCPY = 0x523b0 /\ FP_RET1 = 0x8b7ec /\ FP_RET2 = 0x8b7fc /\
  FP_HDR2 = 0x8b91c /\ FP_SUMQ = 0x8baac.
Proof. repeat split; reflexivity. Qed.

(* diginet_frame_parse's own frame: 48 bytes. *)
Definition FP_FRAME : Z := 48.

(* The frame the prologue writes at entry sp - 48: the caller's s4, s3, s2, s1, s0 and ra at 0 .. 40. *)
Definition fp_fr (c4 c3 c2 c1 c0 cra : word) : list cell := [C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The 64 bytes at f after the two copies: dst and src, then the 52 bytes before the call. *)
Definition fp_copy_cells (b fj : list byte) : list cell := [CB 6 (fr_dst b); CB 6 (fr_src b); CB 52 (skipn 12 fj)].

(* The 64 bytes at f at FP_HDR2: parse_cells (lib/Prog/diginet_frame_parse_c.v) up to the send counter, then the
   40 bytes before the call. *)
Definition fp_hdr1_cells (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b); CB 6 (fr_src b); C2 (Z_to_bv 64 (fr_ethertype b)); CB 2 (firstn 2 (skipn 14 fj));
    C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b)); C4 (Z_to_bv 64 (fr_send b));
    CB 40 (skipn 24 fj) ].

(* The 64 bytes at f at FP_SUMQ: parse_cells up to pad_len, then the 8 bytes before the call. *)
Definition fp_hdr_cells (buf : Z) (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b); CB 6 (fr_src b); C2 (Z_to_bv 64 (fr_ethertype b)); CB 2 (firstn 2 (skipn 14 fj));
    C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b)); C4 (Z_to_bv 64 (fr_send b));
    C4 (Z_to_bv 64 (fr_ack b)); C2 (Z_to_bv 64 (fr_retry b)); C1 (b8 (fr_cmd b)); C1 (b8 (fr_ncmds b));
    C8 (Z_to_bv 64 (buf + 30)); C8 (Z_to_bv 64 (fr_body_len b)); C8 (Z_to_bv 64 (fr_pad_len b));
    CB 8 (skipn 56 fj) ].

(* The range of shadow bytes of [p, p + n) (n > 0). *)
Definition fp_shrng (RNG : ExecF.footprint) (p n : Z) : Prop :=
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1).

(* ---- fp_head_stmt: entry -> the first __asan_memcpy call, or the return ---- *)

(* What the head leaves: the frame written (munch of [sp - 48, sp)); with a code that is not 0, the return to ra
   with a0 = the code and the callee-saved registers as at the entry; with code 0, the call of __asan_memcpy (f,
   buf, 6) from +0x0ec with s0 = f, s1 = buf, s2 = size, s3 = ASAN_K, s4 = numbytes and the frame holding the
   caller's registers. *)
Definition fp_head_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b : list byte) :
    machine_state -> Prop :=
  fun ms' => exists (m1 : word -> option byte) (a1' a2' a3' a4' a5' a6' a7' : word),
    munch [(bv_unsigned sp - FP_FRAME, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    ((fr_code b <> 0 /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr_code b)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m1 (seg_rom rsegs)) \/
     (fr_code b = 0 /\
      rw_cells rsegs m1 (bv_unsigned sp - FP_FRAME) (fp_fr s4 s3 s2 s1 s0 ra) /\
      ms' = MS (mkR (Z_to_bv 64 FP_RET1) (Z_to_bv 64 (bv_unsigned sp - FP_FRAME)) gp tp t0 t1 t2
                    (Z_to_bv 64 f) (Z_to_bv 64 buf) (Z_to_bv 64 f) (Z_to_bv 64 buf) (Z_to_bv 64 6)
                    a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FP_MEMCPY) fc None m1 (seg_rom rsegs))).

Definition fp_head_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f lo : Z) (b : list byte),
    0 < buf -> buf + Z.of_nat (length b) <= 2 ^ 47 -> 0 < f < 2 ^ 64 ->
    bytes_at rsegs m buf b ->
    stk rsegs m lo (bv_unsigned sp) -> lo + FP_FRAME <= bv_unsigned sp ->
    off_stk sp FP_FRAME buf (Z.of_nat (length b)) ->
    app_mem (bv_unsigned sp - FP_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    off_stk sp FP_FRAME GOT_CELL_K 8 -> off_stk sp FP_FRAME CELL_K 8 ->
    addressable m buf (Z.of_nat (length b)) ->
    ExecF.rng RNG (bv_unsigned sp - FP_FRAME) FP_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG buf (Z.of_nat (length b)) ->
    ((30 <= length b)%nat -> fp_shrng RNG buf (Z.of_nat (length b))) ->
    ExecF.evtF rsegs RNG (fp_head_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                            F fc m buf f b)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 f)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_ENTRY) fc None m (seg_rom rsegs)).

(* ---- fp_mid_F: FP_RET1 -> the second __asan_memcpy call (f + 6, buf + 6, 6), ra = FP_RET2 ---- *)
Ltac fp_lit X := let v := eval vm_compute in X in change X with v.
Ltac fp_lits :=
  repeat match goal with
  | |- context [FP_RET1] => fp_lit FP_RET1
  | |- context [FP_RET2] => fp_lit FP_RET2
  | |- context [FP_HDR2] => fp_lit FP_HDR2
  | |- context [FP_SUMQ] => fp_lit FP_SUMQ
  | |- context [FP_MEMCPY] => fp_lit FP_MEMCPY
  | |- context [FP_AT ?o] => fp_lit (FP_AT o)
  | |- context [FP_ENTRY] => fp_lit FP_ENTRY
  end.

Ltac fp_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac fp_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac fp_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac fp_w := fp_shift; fp_usub; fp_shift; fp_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac fp_finF := apply evtF_done; f_equal; fp_regs; fp_w.

Lemma fp_mid_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FP_RET2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned s0 + 6))
                    (Z_to_bv 64 (bv_unsigned s1 + 6)) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  fp_lits.
  do 4 step.
  fp_finF.
Qed.

(* ---- the premises the three runs after the copies share ---- *)

(* The facts of the bytes the runs from FP_RET2 on read or write: the input bytes b at buf and their shadow, the
   64 bytes at f (writable; their cells C) and their shadow, f and the bytes at buf disjoint, both in application
   memory, and the footprint covering both and their shadow bytes. *)
Definition fp_body_pre (RNG : ExecF.footprint) (m : word -> option byte) (buf f : Z) (b : list byte)
    (C : list cell) : Prop :=
  fr_code b = 0 /\
  0 < buf /\ buf + Z.of_nat (length b) <= 2 ^ 47 /\ 0 < f /\ f + 64 <= 2 ^ 47 /\
  bytes_at rsegs m buf b /\ rw_cells rsegs m f C /\ cells_size C = 64%nat /\
  (f + 64 <= buf \/ buf + Z.of_nat (length b) <= f) /\
  addressable m buf (Z.of_nat (length b)) /\ addressable m f 64 /\
  ExecF.rng RNG buf (Z.of_nat (length b)) /\ ExecF.rng RNG f 64 /\
  fp_shrng RNG buf (Z.of_nat (length b)) /\ fp_shrng RNG f 64.

(* ---- fp_hdr1_stmt: FP_RET2 -> FP_HDR2 ---- *)
Definition fp_hdr1_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_copy_cells b fj) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a3' a4' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) a0' (Z_to_bv 64 (buf + 22))
                    (Z_to_bv 64 (fr_sum b)) a3' a4' (Z_to_bv 64 ((buf + 22) / 8)) a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_HDR2) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         fp_body_pre RNG m' buf f b (fp_hdr1_cells b fj))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RET2) fc None m (seg_rom rsegs)).

(* ---- fp_hdr2_stmt: FP_HDR2 -> FP_SUMQ ---- *)
Definition fp_hdr2_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a3 a4 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_hdr1_cells b fj) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) a0' (Z_to_bv 64 (buf + 30))
                    (Z_to_bv 64 (fr_sum b)) (Z_to_bv 64 (fr_body_len b)) a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
                    s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_SUMQ) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         fp_body_pre RNG m' buf f b (fp_hdr_cells buf b fj))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) a0 (Z_to_bv 64 (buf + 22))
               (Z_to_bv 64 (fr_sum b)) a3 a4 (Z_to_bv 64 ((buf + 22) / 8)) a6 a7
               (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
               s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_HDR2) fc None m (seg_rom rsegs)).

(* ---- fp_tail_stmt: FP_SUMQ -> the return ---- *)
(* sq is the sp of the body (the entry sp - 48); the frame [sq, sq + 48) holds the caller's c4 .. c0 and its ra
   cra, outside f. The return: a0 = 0, sp = sq + 48, ra and s0 .. s4 reloaded; the 64 bytes at f are parse_cells. *)
Definition fp_tail_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sq gp tp t0 t1 t2 a0 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c4 c3 c2 c1 c0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_hdr_cells buf b fj) ->
    rw_cells rsegs m (bv_unsigned sq) (fp_fr c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sq + FP_FRAME <= 2 ^ 47 ->
    (f + 64 <= bv_unsigned sq \/ bv_unsigned sq + FP_FRAME <= f) ->
    ExecF.rng RNG (bv_unsigned sq) FP_FRAME ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sq + FP_FRAME)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0)
                    a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' f (parse_cells buf b fj))
      (MS (mkR ra sq gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) a0 (Z_to_bv 64 (buf + 30))
               (Z_to_bv 64 (fr_sum b)) (Z_to_bv 64 (fr_body_len b)) a4 a5 a6 a7
               s2 (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_SUMQ) fc None m (seg_rom rsegs)).
