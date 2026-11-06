(* diginet_frame_parse_segs: the cut points of the image-B walk of diginet_frame_parse (fuzz_frame.asan-ubsan 0x82050 =
   frameb_sigma FB_diginet_frame_parse, 0x53c bytes), and the footprint runs (lib/Lib/ExecF.v evtF, stepped by
   lib/Lib/StepF.v) between them, as statements. lib/B/Prog/diginet_frame_parse_walk.v carries each run into SRr,
   cuts the two __asan_memcpy calls by their contract and the calls of rd32 (two) and diginet_sum16 (one) by their
   leaf statements.

   The runs (offsets from the entry; the neutral listing diginet_frame_parse.fuzz_frame.asan-ubsan.s):
     fp_head_stmt  +0x000 -> the first __asan_memcpy call (+0x120, `jal` 0x50e8c, ra = +0x124), or the return:
                   the 80-byte frame (s7, s6, s5, s4, s3, s2, s1, s0, ra at 8(sp) .. 72(sp); 0(sp) is not written),
                   the null checks (not taken), size < 30 (-2), the UBSan checks of buf + 12 (+0x054, +0x060), the
                   shadow base through GOT_CELL_K -> CELL_K into s5, buf[12], buf[13] (EtherType, -3), the UBSan
                   checks of buf + 14 (+0x0b4, +0x0c0), s3 = buf + 14, buf[14], buf[15] (numbytes, s6; -4), each load
                   after the check of its shadow byte, and the UBSan alignment check of f (+0x10c `andi a0,s0,7`,
                   +0x110 `bnez a0`);
     fp_mid_F      +0x124 -> the second __asan_memcpy call (+0x138, ra = +0x13c): the UBSan check of buf + 6
                   (+0x128), a0 = s0 + 6, a1 = s2 + 6, a2 = 6;
     fp_hdr1_stmt  +0x13c -> the first rd32 call (+0x1e0, `jal` 0x8258c, ra = +0x1e4): the stores of the EtherType
                   (f + 12) and numbytes (f + 16), the UBSan checks of h + 2 (+0x178, +0x184), buf[16], buf[17],
                   s4 = f + 18, s7 = the shadow address of f + 18, the store of the sum (f + 18), the UBSan check of
                   h + 4 (+0x1d8), a0 = buf + 18;
     fp_hdr2_stmt  +0x1e4 -> the second rd32 call (+0x208, ra = +0x20c): the store of rd32's result (the send
                   counter, f + 20), the UBSan check of h + 8 (+0x200), a0 = buf + 22;
     fp_hdr3_stmt  +0x20c -> the diginet_sum16 call (+0x354, `jal` 0x81e30, ra = +0x358): the store of rd32's result
                   (the ack counter, f + 24), the UBSan checks of h + 12 (+0x228, +0x234), retry (f + 28, buf[26..27]),
                   the UBSan check of h + 14 (+0x288), cmd (f + 30, buf[28]), the UBSan check of h + 15 (+0x2c0),
                   num_commands (f + 31, buf[29]), the UBSan check of buf + 30 (+0x2f8), body (f + 32), body_len
                   (f + 40), pad_len (f + 48); a0 = buf + 30, a1 = body_len;
     fp_tail_stmt  +0x358 -> the return: body_sum (f + 56, diginet_sum16's result), the sum read back from f + 18,
                   sum_matches (f + 58), a0 = 0, the epilogue.
   Every load or store of buf or f follows the check of its shadow byte at (a >> 3) + ASAN_K; the addressable
   premises make every check pass, so no errpath_* call (+0x3e4 .. +0x538) is reached. Every branch to the unimp
   word at +0x3d8 is refuted: the pointer-overflow checks by the bound buf + size <= 2^47, the alignment check by
   f mod 8 = 0. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ---- addresses ---- *)
Definition FP_ENTRY : Z := transportb_sigma TB_diginet_frame_parse.
Definition FP_AT (off : Z) : Z := FP_ENTRY + off.
Definition FP_MEMCPY : Z := transportb_sigma TB___asan_memcpy.
Definition FP_RD32 : Z := transportb_sigma TB_rd32.
Definition FP_SUM16 : Z := transportb_sigma TB_diginet_sum16.
(* the return addresses of the two __asan_memcpy calls *)
Definition FP_RET1 : Z := FP_AT 0x124.
Definition FP_RET2 : Z := FP_AT 0x13c.
(* the return addresses of the two rd32 calls and of the diginet_sum16 call *)
Definition FP_RD1R : Z := FP_AT 0x1e4.
Definition FP_RD2R : Z := FP_AT 0x20c.
Definition FP_SUMR : Z := FP_AT 0x358.

Lemma FP_vals : FP_ENTRY = 0x8b1f8 /\ FP_MEMCPY = 0x523ec /\ FP_RD32 = 0x8b734 /\ FP_SUM16 = 0x8afd8 /\
  FP_RET1 = 0x8b31c /\ FP_RET2 = 0x8b334 /\ FP_RD1R = 0x8b3dc /\ FP_RD2R = 0x8b404 /\ FP_SUMR = 0x8b550.
Proof. repeat split; reflexivity. Qed.

(* diginet_frame_parse's own frame: 80 bytes. *)
Definition FP_FRAME : Z := 80.

(* The frame the prologue writes at entry sp - 80: 8 bytes it does not write (j), then the caller's s7, s6, s5, s4,
   s3, s2, s1, s0 and ra at 8 .. 72. *)
Definition fp_fr (j : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [CB 8 j; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The shadow address of f + 18 (s7 from +0x1b4 on): ((f + 18) >> 3) + ASAN_K. *)
Definition fp_sh18 (f : Z) : Z := (f + 18) / 8 + ASAN_K.

(* The 64 bytes at f after the two copies: dst and src, then the 52 bytes before the call. *)
Definition fp_copy_cells (b fj : list byte) : list cell := [CB 6 (fr_dst b); CB 6 (fr_src b); CB 52 (skipn 12 fj)].

(* The 64 bytes at f at the first rd32 call: parse_cells (lib/Prog/diginet_frame_parse_c.v) up to the sum, then the
   44 bytes before the call. *)
Definition fp_hdr1_cells (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b); CB 6 (fr_src b); C2 (Z_to_bv 64 (fr_ethertype b)); CB 2 (firstn 2 (skipn 14 fj));
    C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b)); CB 44 (skipn 20 fj) ].

(* The 64 bytes at f at the second rd32 call: parse_cells up to the send counter, then the 40 bytes before the
   call. *)
Definition fp_hdr2_cells (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b); CB 6 (fr_src b); C2 (Z_to_bv 64 (fr_ethertype b)); CB 2 (firstn 2 (skipn 14 fj));
    C2 (Z_to_bv 64 (fr_numbytes b)); C2 (Z_to_bv 64 (fr_sum b)); C4 (Z_to_bv 64 (fr_send b));
    CB 40 (skipn 24 fj) ].

(* The 64 bytes at f at the diginet_sum16 call: parse_cells up to pad_len, then the 8 bytes before the call. *)
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

(* What the head leaves: the frame written (munch of [sp - 80, sp)); with a code that is not 0, the return to ra
   with a0 = the code and the callee-saved registers as at the entry; with code 0, the call of __asan_memcpy (f,
   buf, 6) from +0x120 with s0 = f, s1 = size, s2 = buf, s3 = buf + 14, s5 = ASAN_K, s6 = numbytes, s4 and s7 as at
   the entry, and the frame holding the caller's registers. *)
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
      (exists j, rw_cells rsegs m1 (bv_unsigned sp - FP_FRAME) (fp_fr j s7 s6 s5 s4 s3 s2 s1 s0 ra)) /\
      ms' = MS (mkR (Z_to_bv 64 FP_RET1) (Z_to_bv 64 (bv_unsigned sp - FP_FRAME)) gp tp t0 t1 t2
                    (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b))) (Z_to_bv 64 f) (Z_to_bv 64 buf)
                    (Z_to_bv 64 6) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) s4 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
                    s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FP_MEMCPY) fc None m1 (seg_rom rsegs))).

Definition fp_head_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f lo : Z) (b : list byte),
    0 < buf -> buf + Z.of_nat (length b) <= 2 ^ 47 -> 0 < f < 2 ^ 64 -> f mod 8 = 0 ->
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
  | |- context [FP_RD1R] => fp_lit FP_RD1R
  | |- context [FP_RD2R] => fp_lit FP_RD2R
  | |- context [FP_SUMR] => fp_lit FP_SUMR
  | |- context [FP_MEMCPY] => fp_lit FP_MEMCPY
  | |- context [FP_RD32] => fp_lit FP_RD32
  | |- context [FP_SUM16] => fp_lit FP_SUM16
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

(* +0x124 li a0,-7; +0x128 bltu a0,s2 to the unimp word (buf + 6 wraps: refuted by buf <= 2^47); +0x12c addi a1,s2,6;
   +0x130 addi a0,s0,6; +0x134 li a2,6; +0x138 jal __asan_memcpy. *)
Lemma fp_mid_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s2 <= 2 ^ 47 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FP_RET2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned s0 + 6))
                    (Z_to_bv 64 (bv_unsigned s2 + 6)) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HS2.
  fp_lits.
  step. step. if_cases HT.
  { exfalso. zify_cond HT. rewrite ?unsigned_lit_wrap in HT. Z.div_mod_to_equations. lia. }
  do 4 step.
  fp_finF.
Qed.

(* ---- the premises the runs after the copies share ---- *)

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

(* ---- fp_hdr1_stmt: FP_RET2 -> the first rd32 call (a0 = buf + 18), ra = FP_RD1R ---- *)
Definition fp_hdr1_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_copy_cells b fj) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 FP_RD1R) sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b)))
                    (Z_to_bv 64 (buf + 18)) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K)
                    (Z_to_bv 64 (fr_numbytes b)) (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_RD32) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         fp_body_pre RNG m' buf f b (fp_hdr1_cells b fj))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b))) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) s4 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (fr_numbytes b))
               s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RET2) fc None m (seg_rom rsegs)).

(* ---- fp_hdr2_stmt: FP_RD1R (a0 = rd32's result, the send counter sign-extended from bit 31) -> the second rd32
   call (a0 = buf + 22), ra = FP_RD2R ---- *)
Definition fp_hdr2_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_hdr1_cells b fj) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 FP_RD2R) sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b)))
                    (Z_to_bv 64 (buf + 22)) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K)
                    (Z_to_bv 64 (fr_numbytes b)) (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_RD32) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         fp_body_pre RNG m' buf f b (fp_hdr2_cells b fj))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b)))
               (sx32 (Z_to_bv 64 (fr_send b))) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (fr_numbytes b)) (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RD1R) fc None m (seg_rom rsegs)).

(* ---- fp_hdr3_stmt: FP_RD2R (a0 = rd32's result, the ack counter sign-extended from bit 31) -> the diginet_sum16
   call (a0 = buf + 30, a1 = body_len), ra = FP_SUMR ---- *)
Definition fp_hdr3_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_hdr2_cells b fj) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 FP_SUMR) sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b)))
                    (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 (fr_body_len b)) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K)
                    (Z_to_bv 64 (fr_numbytes b)) (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 FP_SUM16) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         fp_body_pre RNG m' buf f b (fp_hdr_cells buf b fj))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 (Z.of_nat (length b)))
               (sx32 (Z_to_bv 64 (fr_ack b))) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 14)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (fr_numbytes b)) (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FP_RD2R) fc None m (seg_rom rsegs)).

(* ---- fp_tail_stmt: FP_SUMR (a0 = diginet_sum16's result, the body sum) -> the return ---- *)
(* sq is the sp of the body (the entry sp - 80); the frame [sq, sq + 80) holds 8 bytes j, the caller's c7 .. c0 and
   its ra cra, outside f. The return: a0 = 0, sp = sq + 80, ra and s0 .. s7 reloaded; the 64 bytes at f are
   parse_cells. *)
Definition fp_tail_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sq gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f : Z) (b fj : list byte),
    length fj = 64%nat ->
    fp_body_pre RNG m buf f b (fp_hdr_cells buf b fj) ->
    rw_cells rsegs m (bv_unsigned sq) (fp_fr j c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sq + FP_FRAME <= 2 ^ 47 ->
    (f + 64 <= bv_unsigned sq \/ bv_unsigned sq + FP_FRAME <= f) ->
    ExecF.rng RNG (bv_unsigned sq) FP_FRAME ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sq + FP_FRAME)) gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0)
                    a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m' (seg_rom rsegs) /\
         munch [(f, f + 64)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' f (parse_cells buf b fj))
      (MS (mkR ra sq gp tp t0 t1 t2 (Z_to_bv 64 f) s1 (Z_to_bv 64 (fr_body_sum b)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (f + 18)) (Z_to_bv 64 ASAN_K) s6 (Z_to_bv 64 (fp_sh18 f)) s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 FP_SUMR) fc None m (seg_rom rsegs)).
