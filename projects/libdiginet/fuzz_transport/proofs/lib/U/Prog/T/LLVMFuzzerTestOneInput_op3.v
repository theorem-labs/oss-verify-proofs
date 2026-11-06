(* Case 3 of the op loop of LLVMFuzzerTestOneInput in the ubsan image (fuzz_transport.c:1181-1189), from the case
   entry 0x13af8 to the latch 0x14574. Four straight-line pieces, each a lemma:

     o3_scale  0x13af8 .. 0x13e20  the scale byte: sb = fuzz_u8(&in) (0x13b04; the short-input path 0x13e14 reads
                                   no byte and takes sb = 0), SCALE[sb & 3] from .rodata at 0x10450 (an image
                                   load, so the walk splits on sb mod 4), the cursor into s3 / s6.
     o3_begin  0x13e20 .. 0x13e50  op_begin (TCb.v op_begin_m :390-393): memset(&OW, 0, 0x130) at s9 + 0x158,
                                   memset(&GOT, 0, 0xe0) at s9 + 0x74, lbu g_fail_next, sw -1 into OW.desk_off,
                                   sw it into M.fail. The two memsets are world fills (llvm_mem_after_fill), the
                                   two stores world stores (the kit's hook).
     o3_u16    0x13e50 .. 0x13f90  t = fuzz_u16(&in): no byte left (0x13e74), one byte (0x13e64) or two (0x13f78);
                                   a0 holds the low byte, a1 the high byte shifted by 8.
     o3_tail   0x13f90 .. 0x14574  g_now += scale * t (ld / or / mul / add / sd at s9 + 0x20), m_tick,
                                   diginet_session_tick(&g_s, g_now), a0 = 1, jal settle at 0x14570.

   Every UBSan pointer-overflow check of the case (0x13b00, 0x13b1c, 0x13e58, 0x13f7c; s1 = 1) falls through from
   the bounds of the input buffer and of the SCALE table. The model premise LLVMFuzzerTestOneInput_op_m ... =
   Some (B1, (c2, k1)) fixes every callee's world; the option chain is taken apart with TIoRecv.v's some_pair_inv,
   never with injection on a world-carrying option. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess TOps TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  m_tick_c settle_c diginet_session_tick_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- small facts *)

Lemma o3_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma o3_sub1 : forall (D0 : list byte) k, (k < length D0)%nat -> firstn 1 (skipn k D0) = [nth k D0 (b8 0)].
Proof.
  induction D0 as [|d D0 IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma o3_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma o3_lor_bound : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros n x y Hn Hx Hy.
  assert (Hl : 0 <= Z.lor x y) by (apply Z.lor_nonneg; split; lia).
  split; [exact Hl|].
  assert (E : Z.lor x y = Z.lor x y mod 2 ^ n).
  { rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia.
    rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma o3_scale_range : forall j, 0 <= nth (Z.to_nat j) LLVMFuzzerTestOneInput_SCALE 0 <= 1000000.
Proof.
  intros j. unfold LLVMFuzzerTestOneInput_SCALE.
  destruct (Z.to_nat j) as [|[|[|[|[|n]]]]]; cbn; lia.
Qed.

(* memset's bytes, as its contract leaves them for a1 = 0 *)
Definition o3_z (n : Z) : list byte := repeat (b8 0) (Z.to_nat n).

Lemma o3_z_lenn : forall n, length (o3_z n) = Z.to_nat n.
Proof. intros n. unfold o3_z. apply repeat_length. Qed.

Lemma o3_z_lenz : forall n, 0 <= n -> Z.of_nat (length (o3_z n)) = n.
Proof. intros n Hn. rewrite o3_z_lenn. lia. Qed.

(* the world's length across a write inside it *)
Lemma o3_lu : forall (Bx v : list byte) k, length Bx = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd Bx k v) = Z.to_nat W_LEN.
Proof.
  intros Bx v k L Hk Hv. rewrite length_upd; [exact L | lia |].
  rewrite L, Z2Nat.id by (unfold W_LEN; lia). lia.
Qed.

Ltac o3_wlen L :=
  first [ exact L
        | apply o3_lu; [ o3_wlen L | lia
                       | rewrite ?length_put, ?repeat_length, ?o3_z_lenn; unfold W_LEN; lia ] ].

(* a read of the world outside a write *)
Lemma o3_uo : forall (Bx v : list byte) (k k' : Z) (nn : nat),
  length Bx = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' -> k + Z.of_nat (length v) <= W_LEN ->
  (k' + Z.of_nat nn <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd Bx k v) k' nn = u_at Bx k' nn.
Proof.
  intros Bx v k k' nn L Hk Hk' Hv Hd. apply u_at_upd_out; [lia | lia | lia |].
  rewrite L, Z2Nat.id by (unfold W_LEN; lia). lia.
Qed.

Ltac o3_side L :=
  first [ o3_wlen L
        | (rewrite ?length_put, ?repeat_length, ?o3_z_lenn; unfold W_LEN; lia)
        | lia ].
Ltac o3_push L := repeat (rewrite o3_uo by o3_side L).

(* g_fail_next across a write that misses its byte *)
Lemma o3_gf_out : forall (X v : list byte) k, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd X k v) = g_fail_next X.
Proof.
  intros X v k L Hk Hv Hd. unfold g_fail_next.
  apply o3_uo; [exact L | lia | unfold OFF_g_fail_next; lia | lia | change (Z.of_nat 1) with 1; lia].
Qed.



(* op_begin's world (TCb.v op_begin_m, fuzz_transport.c:388-394) *)
Definition op3_ob (B : list byte) : list byte :=
  let B1 := upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW)) in
  let B2 := upd B1 OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)) in
  let B3 := set_OW_desk_off B2 (-1) in
  set_M_fail B3 (g_fail_next B3).

Lemma op3_ob_eq : forall B, op_begin_m B = Some (op3_ob B, tt).
Proof. intros B. reflexivity. Qed.

Lemma op3_ob_len : forall B, length B = Z.to_nat W_LEN -> length (op3_ob B) = Z.to_nat W_LEN.
Proof.
  intros B L. unfold op3_ob, set_M_fail, set_OW_desk_off, A_M_fail, A_OW_desk_off,
    OFF_M, OFF_OW, OFF_GOT, SZ_OW, SZ_GOT. cbv zeta. o3_wlen L.
Qed.

Lemma op3_ob_gf : forall B, length B = Z.to_nat W_LEN -> g_fail_next (op3_ob B) = g_fail_next B.
Proof.
  intros B L. unfold op3_ob, set_M_fail, set_OW_desk_off, g_fail_next, A_M_fail, A_OW_desk_off,
    OFF_M, OFF_OW, OFF_GOT, OFF_g_fail_next, SZ_OW, SZ_GOT. cbv zeta.
  o3_push L. reflexivity.
Qed.

(* the machine's four writes of op_begin are op_begin_m's world (the two stores in the machine's order) *)
Lemma op3_ob_store : forall B, length B = Z.to_nat W_LEN ->
  upd (upd (upd (upd B 65312 (o3_z 304)) 65084 (o3_z 224)) 65544 (put 4 (-1))) 88
      (put 4 (u_at (upd (upd B 65312 (o3_z 304)) 65084 (o3_z 224)) 64968 1))
  = op3_ob B.
Proof.
  intros B L. unfold op3_ob, set_M_fail, set_OW_desk_off, g_fail_next, A_M_fail, A_OW_desk_off,
    OFF_M, OFF_OW, OFF_GOT, OFF_g_fail_next, SZ_OW, SZ_GOT. cbv zeta.
  change (repeat (b8 0) (Z.to_nat 304)) with (o3_z 304).
  change (repeat (b8 0) (Z.to_nat 224)) with (o3_z 224).
  o3_push L. reflexivity.
Qed.

Lemma o3_gf_now : forall X v, length X = Z.to_nat W_LEN -> g_fail_next (set_g_now X v) = g_fail_next X.
Proof.
  intros X v L. unfold set_g_now. rewrite o3_gf_out;
    [reflexivity | exact L | unfold OFF_g_now; lia
     | rewrite length_put; unfold OFF_g_now, W_LEN; lia
     | rewrite length_put; unfold OFF_g_now, OFF_g_fail_next; lia].
Qed.

Lemma o3_now_len : forall X v, length X = Z.to_nat W_LEN -> length (set_g_now X v) = Z.to_nat W_LEN.
Proof.
  intros X v L. unfold set_g_now. apply o3_lu;
    [exact L | unfold OFF_g_now; lia | rewrite length_put; unfold OFF_g_now, W_LEN; lia].
Qed.

Lemma o3_munch0 : forall (Sp : Z) (m m' : word -> option byte),
  munch [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  munch [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m'.
Proof. intros Sp m m' H x Hx. apply H. cbn [outside] in *. tauto. Qed.

(* a branch whose condition the context decides *)
Ltac o3_br v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v;
      [ cbv iota
      | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec ]
  end.

Section OP3.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* the cursor arithmetic the steps leave, in the model's form *)
Ltac o3_fix c :=
  try (replace (fi_n c + -2) with (fi_n c - 2) by lia);
  try (replace (data + fi_off c + 2) with (data + (fi_off c + 2)) by lia);
  try (replace (data + fi_off c + 1) with (data + (fi_off c + 1)) by lia).

(* The straight-line state of the case at `pc`: s0 the scale, s3 / s6 the cursor, the world B. *)
Definition o3_st (pc : Z) (m0 : word -> option byte) (Sp lo ops scale : Z) (c2 : fuzz_in) (B : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 scale) (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 57) (Z_to_bv 64 (data + fi_off c2)) (Z_to_bv 64 7)
                 s5 (Z_to_bv 64 (fi_n c2)) s7
                 (Z_to_bv 64 209664) (Z_to_bv 64 274632) (Z_to_bv 64 211312) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\
    0 <= fi_off c2 /\ 0 <= fi_n c2 /\ fi_off c2 + fi_n c2 <= Z.of_nat (length D) /\
    llvm_mem data D regs0 m0 Sp lo B m j10 jio j60.

(* 0x13f90, with the two halves of t in a0 / a1. *)
Definition o3_at_t (m0 : word -> option byte) (Sp lo ops scale t : Z) (c3 : fuzz_in) (B : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word) (tlo thi : Z)
         (m : word -> option byte) (j10 jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                 (Z_to_bv 64 scale) (Z_to_bv 64 1)
                 (Z_to_bv 64 tlo) (Z_to_bv 64 thi) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 57) (Z_to_bv 64 (data + fi_off c3)) (Z_to_bv 64 7)
                 s5 (Z_to_bv 64 (fi_n c3)) s7
                 (Z_to_bv 64 209664) (Z_to_bv 64 274632) (Z_to_bv 64 211312) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 81808) fc None m (seg_rom rsegs) /\
    0 <= tlo < 2 ^ 16 /\ 0 <= thi < 2 ^ 16 /\ Z.lor thi tlo = t /\
    0 <= ops < OPS_MAX /\
    0 <= fi_off c3 /\ 0 <= fi_n c3 /\ fi_off c3 + fi_n c3 <= Z.of_nat (length D) /\
    llvm_mem data D regs0 m0 Sp lo B m j10 jio j60.

(* ---------------------------------------------------------------- 0x13af8 .. 0x13e20: the scale byte *)

Lemma o3_scale : forall m0 Sp lo ops c c1 B F fc ms Q,
  llvm_case data D regs0 3 m0 Sp lo ops c c1 B F fc ms ->
  (forall ms',
     o3_st 81440 m0 Sp lo ops
       (nth (Z.to_nat (snd (fuzz_u8_m D c1) mod 4)) LLVMFuzzerTestOneInput_SCALE 0)
       (fst (fuzz_u8_m D c1)) B F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros m0 Sp lo ops c c1 B F fc ms Q H HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & HOPS & HN & HC & HC1 & HI3 & HM).
  pose proof HM as HMu. unfold llvm_mem in HMu.
  destruct HMu as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                   HJ1 & HJ2 & HJ3 & HRW).
  unfold llvm_cursor in HC. unfold LH_K, LH_FRAME in *.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  assert (HU : fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c)))).
  { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  rewrite HU in HC1. cbn [fst] in HC1. subst c1.
  cbn [fi_off fi_n] in HK |- *.
  change (LH_CASE 3) with 80632.
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) with (Z_to_bv 64 209664).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next)) with (Z_to_bv 64 274632).
  change (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) with (Z_to_bv 64 211312).
  change (Z_to_bv 64 0x39) with (Z_to_bv 64 57).
  (* 0x13af8 beqz s6 *)
  step.
  destruct (Z.eqb_spec (fi_n c - 1) 0) as [Hz|Hz].
  - (* the cursor is empty: 0x13e14, SCALE[0] = 1, the cursor unchanged *)
    o3_br true.
    assert (HU1 : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1))
                  = (FuzzIn (fi_off c + 1) (fi_n c - 1), 0)).
    { unfold fuzz_u8_m. cbn [fi_n]. rewrite Hz. reflexivity. }
    rewrite HU1 in HK. cbn [fst snd fi_off fi_n] in HK.
    (* 0x13e14 auipc; 0x13e18 addi; 0x13e1c ld *)
    do 3 step.
    apply HK. unfold o3_st. do 22 eexists. split; [reflexivity|].
    split; [exact HOPS|]. split; [cbn [fi_off]; lia|]. split; [cbn [fi_n]; lia|].
    split; [cbn [fi_off fi_n]; lia|]. exact HM.
  - (* a byte is left: 0x13afc .. 0x13b2c *)
    o3_br false.
    assert (Hn2 : 2 <= fi_n c) by lia.
    assert (HU1 : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1))
                  = (FuzzIn (fi_off c + 2) (fi_n c - 2), at8 D (Z.to_nat (fi_off c + 1)))).
    { unfold fuzz_u8_m. cbn [fi_off fi_n].
      destruct (Z.eqb_spec (fi_n c - 1) 0); [lia|].
      replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
      replace (fi_n c - 1 - 1) with (fi_n c - 2) by lia. reflexivity. }
    rewrite HU1 in HK. cbn [fst snd fi_off fi_n] in HK. unfold at8, bz in HK.
    pose proof (bytes_at_read rsegs m data D (fi_off c + 1) 1 HD ltac:(lia) ltac:(lia)) as HR.
    rewrite o3_sub1 in HR by lia.
    set (bb := nth (Z.to_nat (fi_off c + 1)) D (b8 0)) in *.
    pose proof (o3_byte_range bb) as Rbb.
    assert (Ezx : bv_unsigned (zxb bb) = bv_unsigned bb) by (unfold zxb; apply unsigned_lit; lia).
    (* 0x13afc addi s3; 0x13b00 bgeu s1,s3 *)
    do 2 step. o3_br false.
    (* 0x13b04 lbu a1; 0x13b08 auipc; 0x13b0c addi; 0x13b10 andi *)
    do 4 step.
    rewrite Ezx. rewrite o3_land3 by lia.
    assert (HC4 : bv_unsigned bb mod 4 = 0 \/ bv_unsigned bb mod 4 = 1 \/
                  bv_unsigned bb mod 4 = 2 \/ bv_unsigned bb mod 4 = 3)
      by (pose proof (Z.mod_pos_bound (bv_unsigned bb) 4 ltac:(lia)); lia).
    destruct HC4 as [E4|[E4|[E4|E4]]]; rewrite E4; rewrite E4 in HK;
      (* 0x13b14 slli; 0x13b18 not; 0x13b1c bltu *)
      (do 2 zstep; step; o3_br false;
       (* 0x13b20 addi s6; 0x13b24 addi s3; 0x13b28 add; 0x13b2c j; 0x13e1c ld *)
       do 5 step;
       o3_fix c;
       apply HK; unfold o3_st; do 22 eexists; split; [reflexivity|];
       (split; [exact HOPS|]); (split; [cbn [fi_off]; lia|]); (split; [cbn [fi_n]; lia|]);
       (split; [cbn [fi_off fi_n]; lia|]); exact HM).
Qed.

(* ---------------------------------------------------------------- 0x13e20 .. 0x13e50: op_begin *)

Lemma o3_begin : memset_contract ->
  forall m0 Sp lo ops scale c2 B F fc ms Q,
    o3_st 81440 m0 Sp lo ops scale c2 B F fc ms ->
    (forall ms', o3_st 81488 m0 Sp lo ops scale c2 (op3_ob B) F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.
Proof.
  intros MSC m0 Sp lo ops scale c2 B F fc ms Q HS HK.
  pose proof MSC as MSC0. unfold memset_contract, MEMSET in MSC0.
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s5 & s7 &
                  t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & HOPS & HO2 & HN2 & HON2 & HM).
  pose proof HM as HMu. unfold llvm_mem in HMu.
  destruct HMu as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                   HJ1 & HJ2 & HJ3 & HRW).
  clear HMU HWMO HRW HD HRO HOW HSTK.
  unfold LH_K, LH_FRAME in *.
  pose proof (wm_len rsegs W_BASE_UBSAN m B HWM) as LB.
  wk_facts.
  (* 0x13e20 addi a0,s9,0x158; 0x13e24 li a2,304; 0x13e28 li a1,0; 0x13e2c jal memset *)
  do 4 step.
  assert (U1 : bv_unsigned (Z_to_bv 64 274976) = 274976) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 304) = 304) by (apply unsigned_lit; lia).
  pose proof (wm_piece rsegs W_BASE_UBSAN m B 65312 (bv_unsigned (Z_to_bv 64 304))
                (bv_unsigned (Z_to_bv 64 274976)) HWM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST.
  eapply evt_cut; [ eapply MSC0; [exact DST | exact HMI] | ].
  intros ms1 PO1.
  destruct PO1 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m1 &
                  E1 & MU1 & WMO1 & MI1 & CZ1).
  subst ms1. rewrite U1, U2 in MU1, CZ1.
  rewrite (ret_pc_even 81456) by (first [lia | reflexivity]).
  change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat 304)) with (o3_z 304) in CZ1.
  assert (GF1 : g_fail_next (upd B 65312 (o3_z 304)) <= 1).
  { rewrite (o3_gf_out B (o3_z 304) 65312 LB ltac:(lia)
               ltac:(rewrite o3_z_lenz by lia; unfold W_LEN; lia)
               ltac:(rewrite o3_z_lenz by lia; unfold OFF_g_fail_next; lia)). exact HFN. }
  pose proof (llvm_mem_after_fill data D regs0 m0 Sp lo B m m1 65312 304 (o3_z 304) j10 jio j60
                HM MU1 WMO1 MI1 CZ1 ltac:(lia) ltac:(lia) ltac:(unfold W_LEN; lia) GF1) as HM1.
  clear MU1 WMO1 CZ1 HWM HMI DST.
  assert (LB1 : length (upd B 65312 (o3_z 304)) = Z.to_nat W_LEN)
    by (apply o3_lu; [exact LB | lia | rewrite o3_z_lenz by lia; unfold W_LEN; lia]).
  pose proof HM1 as HM1u. unfold llvm_mem in HM1u.
  destruct HM1u as (zD0 & zDL & zOW & zD & zSP & zSTK & zLO & zSP2 & zWL & zMI & zRO & zWM & zFN & zMU & zWMO &
                    zJ1 & zJ2 & zJ3 & zRW).
  clear zD0 zDL zOW zD zSP zSTK zLO zSP2 zWL zRO zMU zWMO zJ1 zJ2 zJ3 zRW.
  (* 0x13e30 addi a0,s9,0x74; 0x13e34 li a2,224; 0x13e38 li a1,0; 0x13e3c jal memset *)
  do 4 step.
  assert (U3 : bv_unsigned (Z_to_bv 64 274748) = 274748) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 224) = 224) by (apply unsigned_lit; lia).
  pose proof (wm_piece rsegs W_BASE_UBSAN m1 (upd B 65312 (o3_z 304)) 65084 (bv_unsigned (Z_to_bv 64 224))
                (bv_unsigned (Z_to_bv 64 274748)) zWM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as DST2.
  eapply evt_cut; [ eapply MSC0; [exact DST2 | exact zMI] | ].
  intros ms2 PO2.
  destruct PO2 as (w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 &
                  E2 & MU2 & WMO2 & MI2 & CZ2).
  subst ms2. rewrite U3, U4 in MU2, CZ2.
  rewrite (ret_pc_even 81472) by (first [lia | reflexivity]).
  change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat 224)) with (o3_z 224) in CZ2.
  assert (GF2 : g_fail_next (upd (upd B 65312 (o3_z 304)) 65084 (o3_z 224)) <= 1).
  { rewrite (o3_gf_out (upd B 65312 (o3_z 304)) (o3_z 224) 65084 LB1 ltac:(lia)
               ltac:(rewrite o3_z_lenz by lia; unfold W_LEN; lia)
               ltac:(rewrite o3_z_lenz by lia; unfold OFF_g_fail_next; lia)). exact zFN. }
  pose proof (llvm_mem_after_fill data D regs0 m0 Sp lo (upd B 65312 (o3_z 304)) m1 m2 65084 224 (o3_z 224)
                j10 jio j60 HM1 MU2 WMO2 MI2 CZ2 ltac:(lia) ltac:(lia) ltac:(unfold W_LEN; lia) GF2) as HM2.
  clear MU2 WMO2 CZ2 zWM zMI zFN.
  assert (LB2 : length (upd (upd B 65312 (o3_z 304)) 65084 (o3_z 224)) = Z.to_nat W_LEN)
    by (apply o3_lu; [exact LB1 | lia | rewrite o3_z_lenz by lia; unfold W_LEN; lia]).
  pose proof HM2 as HM2u. unfold llvm_mem in HM2u.
  destruct HM2u as (q1 & q2 & q3 & q4 & q5 & qSTK & q7 & q8 & q9 & qMI & q11 & qWM & qFN & q14 & q15 &
                    q16 & q17 & q18 & q19).
  clear q1 q2 q3 q4 q5 q7 q8 q9 q11 q14 q15 q16 q17 q18 q19.
  pose proof (munch_refl [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m2) as MUw.
  pose proof (wmono_refl rsegs m2) as WMOw.
  (* 0x13e40 lbu a0,0(s9); 0x13e44 li a1,-1; 0x13e48 sw a1,0x240(s9); 0x13e4c sw a0,0x58(s8) *)
  do 4 step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | HW : rw_cells rsegs mm W_BASE_UBSAN [CB _ ?BW] |- _ =>
          assert (EOB : BW = op3_ob B) by (apply op3_ob_store; exact LB);
          rewrite EOB in HW
      end
  end.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | HW : rw_cells rsegs mm W_BASE_UBSAN [CB _ (op3_ob B)], HI : mem_inv rsegs mm,
        MU : munch [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m2 mm, WO : wmono rsegs m2 mm,
        SK : stk rsegs mm lo Sp |- _ =>
          assert (HM3 : llvm_mem data D regs0 m0 Sp lo (op3_ob B) mm j10 jio j60)
            by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0
                          (upd (upd B 65312 (o3_z 304)) 65084 (o3_z 224)) (op3_ob B) m2 mm);
                [ exact HM2 | unfold LH_K; lia | exact (o3_munch0 Sp m2 mm MU)
                | exact WO | exact HI | exact SK | exact HW
                | rewrite (op3_ob_gf B LB); exact HFN ])
      end
  end.
  apply HK. unfold o3_st. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [lia|]. split; [lia|]. split; [lia|]. exact HM3.
Qed.

(* ---------------------------------------------------------------- 0x13e50 .. 0x13f90: the u16 *)

Lemma o3_u16 : forall m0 Sp lo ops scale c2 B F fc ms Q,
  o3_st 81488 m0 Sp lo ops scale c2 B F fc ms ->
  (forall ms' c3 t, fuzz_u16_m D c2 = (c3, t) ->
     o3_at_t m0 Sp lo ops scale t c3 B F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros m0 Sp lo ops scale c2 B F fc ms Q HS HK.
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s5 & s7 &
                  t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & HOPS & HO2 & HN2 & HON2 & HM).
  pose proof HM as HMu. unfold llvm_mem in HMu.
  destruct HMu as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                   HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  (* 0x13e50 beqz s6 *)
  step.
  destruct (Z.eqb_spec (fi_n c2) 0) as [Hz0|Hz0].
  - (* no byte: t = 0, the cursor unchanged *)
    o3_br true.
    assert (HU0 : fuzz_u8_m D c2 = (c2, 0)) by (unfold fuzz_u8_m; rewrite Hz0; reflexivity).
    assert (HT : fuzz_u16_m D c2 = (c2, 0)).
    { unfold fuzz_u16_m. rewrite HU0. cbv beta iota zeta. rewrite HU0. reflexivity. }
    (* 0x13e74 mv a0,zero; 0x13e78 mv a1,zero; 0x13e7c j *)
    do 3 step.
    eapply HK; [exact HT|].
    unfold o3_at_t. do 22 eexists. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [reflexivity|].
    split; [exact HOPS|]. split; [lia|]. split; [lia|]. split; [lia|]. exact HM.
  - o3_br false.
    pose proof (bytes_at_read rsegs m data D (fi_off c2) 1 HD ltac:(lia) ltac:(lia)) as HR0.
    rewrite o3_sub1 in HR0 by lia.
    set (b0 := nth (Z.to_nat (fi_off c2)) D (b8 0)) in *.
    pose proof (o3_byte_range b0) as Rb0.
    assert (HU0 : fuzz_u8_m D c2 = (FuzzIn (fi_off c2 + 1) (fi_n c2 - 1), bv_unsigned b0)).
    { unfold fuzz_u8_m. rewrite (proj2 (Z.eqb_neq (fi_n c2) 0) Hz0). reflexivity. }
    (* 0x13e54 addi a2,s3,1; 0x13e58 bgeu s1,a2 *)
    do 2 step. o3_br false.
    (* 0x13e5c lbu a0,0(s3); 0x13e60 bne s6,s1 *)
    do 2 step.
    change (zxb b0) with (Z_to_bv 64 (bv_unsigned b0)).
    destruct (Z.eqb_spec (fi_n c2) 1) as [H1|H1].
    + (* one byte: t = the byte *)
      o3_br false.
      assert (HU1 : fuzz_u8_m D (FuzzIn (fi_off c2 + 1) (fi_n c2 - 1))
                    = (FuzzIn (fi_off c2 + 1) (fi_n c2 - 1), 0)).
      { unfold fuzz_u8_m. cbn [fi_n].
        replace (fi_n c2 - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      assert (HT : fuzz_u16_m D c2 = (FuzzIn (fi_off c2 + 1) 0, bv_unsigned b0)).
      { unfold fuzz_u16_m. rewrite HU0. cbv beta iota zeta. rewrite HU1. cbv beta iota zeta.
        replace (fi_n c2 - 1) with 0 by lia.
        f_equal. change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r. apply Z.mod_small. lia. }
      (* 0x13e64 mv s6,zero; 0x13e68 mv a1,zero; 0x13e6c mv s3,a2; 0x13e70 j *)
      do 4 step.
      o3_fix c2.
      eapply HK; [exact HT|].
      unfold o3_at_t. do 22 eexists. split; [cbn [fi_off fi_n]; reflexivity|].
      split; [lia|]. split; [lia|]. split; [apply Z.lor_0_l|].
      split; [exact HOPS|]. split; [cbn [fi_off]; lia|]. split; [cbn [fi_n]; lia|].
      split; [cbn [fi_off fi_n]; lia|]. exact HM.
    + (* two bytes or more *)
      o3_br true.
      assert (Hn2 : 2 <= fi_n c2) by lia.
      pose proof (bytes_at_read rsegs m data D (fi_off c2 + 1) 1 HD ltac:(lia) ltac:(lia)) as HR1.
      rewrite o3_sub1 in HR1 by lia.
      set (b1 := nth (Z.to_nat (fi_off c2 + 1)) D (b8 0)) in *.
      pose proof (o3_byte_range b1) as Rb1.
      assert (Ez1 : bv_unsigned (zxb b1) = bv_unsigned b1) by (unfold zxb; apply unsigned_lit; lia).
      assert (Hsh : 0 <= Z.shiftl (bv_unsigned b1) 8 < 2 ^ 16)
        by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      assert (HU1 : fuzz_u8_m D (FuzzIn (fi_off c2 + 1) (fi_n c2 - 1))
                    = (FuzzIn (fi_off c2 + 1 + 1) (fi_n c2 - 1 - 1), bv_unsigned b1)).
      { unfold fuzz_u8_m. cbn [fi_off fi_n].
        replace (fi_n c2 - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      assert (HT : fuzz_u16_m D c2
                   = (FuzzIn (fi_off c2 + 2) (fi_n c2 - 2),
                      Z.lor (Z.shiftl (bv_unsigned b1) 8) (bv_unsigned b0))).
      { unfold fuzz_u16_m. rewrite HU0. cbv beta iota zeta. rewrite HU1. cbv beta iota zeta.
        replace (fi_off c2 + 1 + 1) with (fi_off c2 + 2) by lia.
        replace (fi_n c2 - 1 - 1) with (fi_n c2 - 2) by lia.
        f_equal. rewrite (Z.lor_comm (bv_unsigned b0) (Z.shiftl (bv_unsigned b1) 8)).
        apply Z.mod_small. apply (o3_lor_bound 16); [lia | exact Hsh | lia]. }
      (* 0x13f78 addi a2,a2,1; 0x13f7c bgeu s1,a2 *)
      do 2 step. o3_br false.
      (* 0x13f80 lbu a1,1(s3); 0x13f84 addi s6,s6,-2; 0x13f88 addi s3,s3,2; 0x13f8c slli a1,a1,8 *)
      do 4 step.
      rewrite Ez1.
      o3_fix c2.
      eapply HK; [exact HT|].
      unfold o3_at_t. do 22 eexists. split; [cbn [fi_off fi_n]; reflexivity|].
      split; [lia|]. split; [exact Hsh|]. split; [reflexivity|].
      split; [exact HOPS|]. split; [cbn [fi_off]; lia|]. split; [cbn [fi_n]; lia|].
      split; [cbn [fi_off fi_n]; lia|]. exact HM.
Qed.

(* ---------------------------------------------------------------- 0x13f90 .. 0x14574: the tail *)

Lemma o3_tail : m_tick_contract -> diginet_session_tick_contract -> settle_contract ->
  forall m0 Sp lo ops scale t c3 Bo B3 B4 B5 u3 r4 u5 F fc ms,
    o3_at_t m0 Sp lo ops scale t c3 Bo F fc ms ->
    0 <= scale <= 1000000 ->
    m_tick_m (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) = Some (B3, u3) ->
    diginet_session_tick_m timg_ubsan None B3 (g_now B3) = Some (B4, r4) ->
    settle_m B4 1 = Some (B5, u5) ->
    evt rsegs (llvm_latch data D regs0 m0 Sp lo ops c3 B5 F fc) ms.
Proof.
  intros MT MTK MSE m0 Sp lo ops scale t c3 Bo B3 B4 B5 u3 r4 u5 F fc ms HS HSC HMT HTK HST.
  destruct u3. destruct u5.
  pose proof MT as MT0. unfold m_tick_contract, m_tick_ENTRY, m_tick_FRAME in MT0.
  pose proof MTK as MTK0.
  unfold diginet_session_tick_contract, diginet_session_tick_ENTRY, diginet_session_tick_FRAME in MTK0.
  pose proof MSE as MSE0. unfold settle_contract, settle_ENTRY, settle_FRAME in MSE0.
  destruct HS as (ra & t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s5 & s7 & t3 & t4 & t5 & t6 &
                  tlo & thi & m & j10 & jio & j60 & -> & Rlo & Rhi & Et & HOPS & HO3 & HN3 & HON3 & HM).
  pose proof HM as HMu. unfold llvm_mem in HMu.
  destruct HMu as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                   HJ1 & HJ2 & HJ3 & HRW).
  clear HMU HWMO HRW HD HOW.
  unfold LH_K, LH_FRAME in *.
  pose proof HSTK as HSTK0. destruct HSTK0 as (Hlo0 & Hhi0 & _).
  pose proof (wm_len rsegs W_BASE_UBSAN m Bo HWM) as LB.
  pose proof (u_at_range Bo OFF_g_now 8) as Rg.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rg.
  change (u_at Bo OFF_g_now 8) with (g_now Bo) in Rg.
  assert (Rt : 0 <= t < 2 ^ 16) by (rewrite <- Et; apply (o3_lor_bound 16); [lia | exact Rhi | exact Rlo]).
  assert (Rts : 0 <= t * scale < 2 ^ 64).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    apply Z.le_lt_trans with (65536 * 1000000); [apply Z.mul_le_mono_nonneg; lia | lia]. }
  assert (HSpu : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  wk_facts.
  pose proof (munch_refl [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MUw.
  pose proof (wmono_refl rsegs m) as WMOw.
  (* 0x13f90 ld a2,0x20(s9) *)
  step.
  change (u_at Bo 65000 8) with (g_now Bo).
  (* 0x13f94 or a0,a1,a0 *)
  step. rewrite (unsigned_lit thi) by lia. rewrite (unsigned_lit tlo) by lia. rewrite Et.
  (* 0x13f98 mul a0,a0,s0 *)
  step. rewrite (unsigned_lit t) by lia. rewrite (unsigned_lit scale) by lia.
  (* 0x13f9c add a0,a0,a2 *)
  step. rewrite ?(unsigned_lit (t * scale)) by lia.
  (* 0x13fa0 sd a0,0x20(s9) *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | HW : rw_cells rsegs mm W_BASE_UBSAN [CB _ (upd Bo 65000 (put 8 ?X))] |- _ =>
          assert (EW : upd Bo 65000 (put 8 X) = set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64));
          [ unfold set_g_now, OFF_g_now; f_equal;
            rewrite (put_mod64 8 (g_now Bo + scale * t)) by lia; f_equal;
            rewrite ?unsigned_lit by lia; first [ring | lia]
          | rewrite EW in HW ]
      end
  end.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | HW : rw_cells rsegs mm W_BASE_UBSAN [CB _ (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64))],
        HI : mem_inv rsegs mm, MU : munch [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm,
        WO : wmono rsegs m mm, SK : stk rsegs mm lo Sp |- _ =>
          assert (HMa : llvm_mem data D regs0 m0 Sp lo
                          (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) mm j10 jio j60)
            by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 Bo
                          (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) m mm);
                [ exact HM | unfold LH_K; lia | exact (o3_munch0 Sp m mm MU)
                | exact WO | exact HI | exact SK | exact HW
                | rewrite (o3_gf_now Bo _ LB); exact HFN ])
      end
  end.
  clear MUw WMOw.
  pose proof HMa as HMau. unfold llvm_mem in HMau.
  destruct HMau as (aD0 & aDL & aOW & aD & aSP & aSTK & aLO & aSP2 & aWL & aMI & aRO & aWM & aFN & aMU & aWMO &
                    aJ1 & aJ2 & aJ3 & aRW).
  clear aD0 aDL aOW aD aSP aLO aSP2 aWL aMU aWMO aJ1 aJ2 aJ3 aRW.
  assert (LBa : length (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) = Z.to_nat W_LEN)
    by (apply o3_now_len; exact LB).
  (* 0x13fa4 jal m_tick *)
  step.
  eapply evt_cut;
  [ eapply MT0 with (lo := lo) (B := set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) (B' := B3);
    [ rewrite HSpu; exact HSP
    | rewrite HSpu; exact aSTK
    | rewrite HSpu; lia
    | unfold w_off_stack; rewrite HSpu; lia
    | exact aMI
    | exact aWM
    | exact HMT ]
  | ].
  intros msA POA.
  destruct POA as (p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & p14 & p15 & mA &
                  EA & MUA & WMOA & MIA & STA & WMA).
  subst msA. rewrite HSpu in MUA, STA.
  rewrite (ret_pc_even 81832) by (first [lia | reflexivity]).
  assert (GF3 : g_fail_next B3 <= 1).
  { pose proof (m_tick_gk (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) LBa
                  (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) B3 tt
                  (gkeep_refl _) HMT) as GK.
    destruct GK as (_ & GKf). rewrite GKf. rewrite (o3_gf_now Bo _ LB). exact HFN. }
  assert (HMb : llvm_mem data D regs0 m0 Sp lo B3 mA j10 jio j60)
    by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0
                  (set_g_now Bo ((g_now Bo + scale * t) mod 2 ^ 64)) B3 _ mA);
        [ exact HMa | unfold LH_K; lia | exact MUA | exact WMOA | exact MIA | exact STA | exact WMA
        | exact GF3 ]).
  clear aWM aMI aSTK aRO aFN MUA WMOA.
  pose proof HMb as HMbu. unfold llvm_mem in HMbu.
  destruct HMbu as (bD0 & bDL & bOW & bD & bSP & bSTK & bLO & bSP2 & bWL & bMI & bRO & bWM & bFN & bMU & bWMO &
                    bJ1 & bJ2 & bJ3 & bRW).
  clear bD0 bDL bOW bD bSP bLO bSP2 bWL bMU bWMO bJ1 bJ2 bJ3 bRW.
  pose proof (u_at_range B3 OFF_g_now 8) as Rg3.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rg3.
  change (u_at B3 OFF_g_now 8) with (g_now B3) in Rg3.
  (* 0x13fa8 ld a1,0x20(s9); 0x13fac auipc a0; 0x13fb0 addi a0; 0x13fb4 jal diginet_session_tick *)
  step.
  change (u_at B3 65000 8) with (g_now B3).
  do 3 step.
  eapply evt_cut;
  [ eapply MTK0 with (lo := lo) (now := g_now B3) (B := B3) (B' := B4) (r := r4) (TF := None);
    [ reflexivity | reflexivity | exact Rg3 | exact bWM | exact GF3 | exact HTK
    | exact I
    | exact bRO
    | rewrite HSpu; exact HSP
    | rewrite HSpu; exact bSTK
    | rewrite HSpu; lia
    | unfold w_off_stack; rewrite HSpu; lia
    | exact bMI ]
  | ].
  intros msB POB.
  destruct POB as (r1 & r2 & r3 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & mB &
                  EB & MUB & WMOB & MIB & STB & WMB & GFB).
  subst msB. rewrite HSpu in MUB, STB.
  rewrite (ret_pc_even 81848) by (first [lia | reflexivity]).
  assert (HMc : llvm_mem data D regs0 m0 Sp lo B4 mB j10 jio j60)
    by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 2144 B3 B4 _ mB);
        [ exact HMb | unfold LH_K; lia | exact MUB | exact WMOB | exact MIB | exact STB | exact WMB
        | exact GFB ]).
  clear bWM bMI bSTK bRO bFN MUB WMOB.
  pose proof HMc as HMcu. unfold llvm_mem in HMcu.
  destruct HMcu as (cD0 & cDL & cOW & cD & cSP & cSTK & cLO & cSP2 & cWL & cMI & cRO & cWM & cFN & cMU & cWMO &
                    cJ1 & cJ2 & cJ3 & cRW).
  clear cD0 cDL cOW cD cSP cLO cSP2 cWL cMU cWMO cJ1 cJ2 cJ3 cRW.
  (* 0x13fb8 addi a0,zero,1; 0x13fbc j 0x14570; 0x14570 jal settle *)
  do 3 step.
  eapply evt_cut;
  [ eapply MSE0 with (lo := lo) (B := B4) (B' := B5) (ticked := 1);
    [ reflexivity | lia | exact cWM | exact HST
    | rewrite HSpu; exact HSP
    | rewrite HSpu; exact cSTK
    | rewrite HSpu; lia
    | unfold w_off_stack; rewrite HSpu; lia
    | exact cMI ]
  | ].
  intros msC POC.
  destruct POC as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & mC &
                  EC & MUC & WMOC & MIC & STC & EB5 & WMC).
  subst msC. rewrite HSpu in MUC, STC.
  rewrite (ret_pc_even 83316) by (first [lia | reflexivity]).
  assert (HMd : llvm_mem data D regs0 m0 Sp lo B4 mC j10 jio j60)
    by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 96 B4 B4 _ mC);
        [ exact HMc | unfold LH_K; lia | exact (lh_munch_add_world (Sp - 96) Sp _ mC MUC)
        | exact WMOC | exact MIC | exact STC | exact WMC | exact cFN ]).
  apply evt_done. unfold llvm_latch. rewrite EB5.
  do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [unfold llvm_cursor; split; [lia | split; lia]|].
  exact HMd.
Qed.

End OP3.

(* ---------------------------------------------------------------- the statement *)

Theorem llvm_op3_holds :
  memset_contract -> m_tick_contract -> diginet_session_tick_contract -> settle_contract -> llvm_op_stmt 3.
Proof.
  intros MSC MT MTK MSE.
  unfold llvm_op_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms A k B1 c2 k1 HCASE HOP.
  pose proof HCASE as HC0. unfold llvm_case in HC0.
  destruct HC0 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                   ? & ? & ? & ? & HC1 & HI3 & ?).
  unfold LLVMFuzzerTestOneInput_op_m in HOP.
  destruct (fuzz_u8_m D c) as [cu1 opb] eqn:HU.
  rewrite ?HU in HC1, HI3, HOP. cbn [fst snd] in HC1, HI3.
  subst c1.
  cbv beta iota zeta in HOP.
  rewrite HI3 in HOP.
  cbv beta iota zeta delta [Z.eqb Pos.eqb] in HOP.
  destruct (fuzz_u8_m D cu1) as [cu2 sb] eqn:HU2.
  rewrite ?HU2 in HOP. cbv beta iota zeta in HOP.
  rewrite op3_ob_eq in HOP. cbv beta iota zeta in HOP.
  destruct (fuzz_u16_m D cu2) as [cu3 tv] eqn:HU16.
  rewrite ?HU16 in HOP. cbv beta iota zeta in HOP.
  lazymatch type of HOP with
  | context [m_tick_m ?X] => destruct (m_tick_m X) as [[B3 u3]|] eqn:HMT
  end.
  2: { rewrite ?HMT in HOP. cbv beta iota in HOP. discriminate HOP. }
  rewrite ?HMT in HOP. cbv beta iota in HOP.
  lazymatch type of HOP with
  | context [diginet_session_tick_m ?I ?TF ?X ?N] =>
      destruct (diginet_session_tick_m I TF X N) as [[B4 r4]|] eqn:HTK
  end.
  2: { rewrite ?HTK in HOP. cbv beta iota in HOP. discriminate HOP. }
  rewrite ?HTK in HOP. cbv beta iota in HOP.
  lazymatch type of HOP with
  | context [settle_m ?X ?T] => destruct (settle_m X T) as [[B5 u5]|] eqn:HST
  end.
  2: { rewrite ?HST in HOP. cbv beta iota in HOP. discriminate HOP. }
  rewrite ?HST in HOP. cbv beta iota in HOP.
  apply some_pair_inv in HOP. destruct HOP as [EB Ec].
  injection Ec as Ec1 Ec2. subst B1. subst c2. subst k1.
  (* the walk *)
  eapply (o3_scale data D regs0); [exact HCASE|].
  intros ms1 HS1.
  rewrite HU2 in HS1. cbn [fst snd] in HS1.
  eapply (o3_begin data D regs0 MSC); [exact HS1|].
  intros ms2 HS2.
  eapply (o3_u16 data D regs0); [exact HS2|].
  intros ms3 cc3 tt3 HTeq HS3.
  rewrite HU16 in HTeq. injection HTeq as Ee1 Ee2. subst cc3. subst tt3.
  eapply (o3_tail data D regs0 MT MTK MSE) with (B3 := B3) (B4 := B4) (B5 := B5);
    [ exact HS3
    | apply o3_scale_range
    | exact HMT
    | exact HTK
    | exact HST ].
Qed.
