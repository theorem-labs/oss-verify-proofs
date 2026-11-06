(* Cases 0 and 8 of the op loop of LLVMFuzzerTestOneInput in the plain image, at the SR level (fuzz_transport.c:1168-1171
   `case 0: receive(p, fuzz_record(&in, &p), 0, 0)` and :1206-1211 `default: receive(p, fuzz_record(&in, &p), 1, pf)`
   with pf = fuzz_u8(&in) read first). Both read a record of the input and call receive, an SR contract (receive_c.v),
   so each case is three pieces (_sr.v, TSRGlue.v): an evt segment from the case entry to receive's entry (g_run),
   the call (llvm_sr_rec: receive_contract, sr_fr_call, llvm_mem_sr_call), and an evt segment from receive's return
   to the latch (g_run, which runs sr_run_norm). The model is TOps.v LLVMFuzzerTestOneInput_op_m's op =? 0 branch
   and its last branch.

   The machine, from tr6/llvmf-plain.dis (s4 / s7 the cursor before the op byte, s3 / s6 after it):
     case 0  0x138f0 beqz s6 -> 0x13b3c (n = 0: u16 = 0); 0x138f4 lbu a0, 1(s4) (the u16's low byte);
             0x138fc bne s7, 2 -> 0x13c54 (lbu a1, 2(s4), the high byte; s7 -= 3; s3 = s4 + 3; a1 <<= 8);
             else 0x13900 (one byte: s7 = 0, a1 = 0, s3 = s4 + 2); all join 0x13c64, the take and the call
             receive(s3, n, 0, 0) at 0x13f54.
     case 8  0x13ac0 beqz s6 -> 0x13b60 (n = 0: pf = 0, u16 = 0); 0x13ac4 lbu a3, 1(s4) (pf);
             0x13acc bne s7, 2 -> 0x13ca4 (lbu a0, 2(s4), the low byte; 0x13cac bne s7, 3 -> 0x13f28: lbu a1, 3(s4),
             the high byte, s7 -= 4, s3 = s4 + 4, a1 <<= 8; else 0x13cb0: s7 = 0, a1 = 0, s3 = s4 + 3);
             else 0x13ad0 (pf only: s7 = 0, a0 = a1 = 0, s3 = s4 + 2); all join 0x13f38, the take and the call
             receive(s3, n, 1, pf) at 0x13f54.
     return  0x13f58 j 0x14288; 0x14288 mv s3, s0 (the cursor after the record); the latch 0x1428c. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c TSRGlue
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_disp LLVMFuzzerTestOneInput_sr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_take_m's count (fuzz.h:63-70): n = min(want, in->n) *)
Definition op08_take (w rem : Z) : Z := if w <? rem then w else rem.

(* fuzz_record_m from fuzz_u16_m's result *)
Lemma op08_rec_u16 : forall D c off rem w, fuzz_u16_m D c = (FuzzIn off rem, w) ->
  fuzz_record_m D c = (FuzzIn (off + op08_take w rem) (rem - op08_take w rem), off, op08_take w rem).
Proof. intros D c off rem w H. unfold fuzz_record_m. rewrite H. reflexivity. Qed.

Section OP08E.
Context (data : Z) (D : list byte).

(* The state at receive's entry 0x14afc (receive_c.v receive_ENTRY; the dis: `jal 0xba8 -> 0x14afc <receive>`) after
   the jal at 0x13f54 (ra = 0x13f58): a0 = p, a1 = n, a2 = by_poll, a3 = poll_flags; s0 / s6 the cursor after the
   record (0x13c70-0x13c74, 0x13f44-0x13f48); s1 = 7, s2 = 0x39, s5 = &g_s, s8 = 1, s9, s10, s11 = ops are the loop's
   (_lh.v llvm_case), kept by the case. *)
Definition op08_call (Sp ops : Z) (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m : word -> option byte)
    (p n : Z) (cA : fuzz_in) (bp pf : Z) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a4 a5 a6 a7 w19 w20 w23 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 0x13f58) (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 (data + fi_off cA))
                 (Z_to_bv 64 7) (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 bp) (Z_to_bv 64 pf) a4 a5 a6 a7
                 (Z_to_bv 64 0x39) w19 w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n cA)) w23
                 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
                 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 receive_ENTRY) fc None m (seg_rom rsegs).

(* the end of the record's take and the call, shared by every cursor length:
   0x13c64 or a1, a1, a0 (the u16, lo | hi << 8); 0x13c68 bltu a1, s7 -> 0x13c70; 0x13c6c mv a1, s7 (n = min);
   0x13c70 add s0, s3, a1; 0x13c74 sub s6, s7, a1 (the cursor after the take); 0x13c78 mv a0, s3 (p);
   0x13c7c mv a2, zero; 0x13c80 mv a3, zero (receive(p, n, 0, 0)); 0x13c84 j 0x13f54; 0x13f54 jal receive *)
Lemma op0_join : forall Sp ops F fc m rz gp tp e0 e1 e2 x8 wlo whi q2 q3 q4 q5 q6 q7 w19 w20 w22 w23
    e3 e4 e5 e6 off rem w,
  0 <= rem < 2 ^ 64 ->
  w19 = Z_to_bv 64 (data + off) -> w23 = Z_to_bv 64 rem ->
  Z.lor (bv_unsigned whi) (bv_unsigned wlo) = w -> 0 <= w < 2 ^ 16 ->
  evt rsegs (op08_call Sp ops F fc gp tp m (data + off) (op08_take w rem)
               (FuzzIn (off + op08_take w rem) (rem - op08_take w rem)) 0 0)
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 x8 (Z_to_bv 64 7) wlo whi q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 0x39) w19 w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22 w23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13c64) fc None m (seg_rom rsegs)).
Proof.
  intros Sp ops F fc m rz gp tp e0 e1 e2 x8 wlo whi q2 q3 q4 q5 q6 q7 w19 w20 w22 w23 e3 e4 e5 e6 off rem w
    Hr H19 H23 HW Hw.
  subst w19 w23.
  zstep. zstep.
  rewrite HW.
  if_cases K; zify_cond K.
  - (* n = w: 0x13c70 add, 0x13c74 sub, 0x13c78 mv a0, 0x13c7c-0x13c80 a2 = a3 = 0, 0x13c84 j, 0x13f54 jal *)
    assert (Kw : w < rem) by (rewrite ?Z.mod_small in K by lia; lia).
    assert (En : op08_take w rem = w) by (unfold op08_take; destruct (Z.ltb_spec w rem); lia).
    do 7 zstep.
    apply evt_done. unfold op08_call. cbn [fi_off fi_n]. rewrite En.
    do 14 eexists.
    replace (data + (off + w)) with (data + off + w) by lia.
    reflexivity.
  - (* n = rem: 0x13c6c mv a1, s7, then the same seven *)
    assert (Kw : rem <= w) by (rewrite ?Z.mod_small in K by lia; lia).
    assert (En : op08_take w rem = rem) by (unfold op08_take; destruct (Z.ltb_spec w rem); lia).
    do 8 zstep.
    apply evt_done. unfold op08_call. cbn [fi_off fi_n]. rewrite En.
    do 14 eexists.
    replace (data + (off + rem)) with (data + off + rem) by lia.
    reflexivity.
Qed.

(* the same for case 8: 0x13f38 or a1, a1, a0; 0x13f3c bltu a1, s7 -> 0x13f44; 0x13f40 mv a1, s7;
   0x13f44 add s0, s3, a1; 0x13f48 sub s6, s7, a1; 0x13f4c li a2, 1; 0x13f50 mv a0, s3
   (receive(p, n, 1, pf), a3 = pf from before); 0x13f54 jal receive *)
Lemma op8_join : forall Sp ops F fc m rz gp tp e0 e1 e2 x8 wlo whi q2 wpf q4 q5 q6 q7 w19 w20 w22 w23
    e3 e4 e5 e6 off rem w pf,
  0 <= rem < 2 ^ 64 ->
  w19 = Z_to_bv 64 (data + off) -> w23 = Z_to_bv 64 rem -> wpf = Z_to_bv 64 pf ->
  Z.lor (bv_unsigned whi) (bv_unsigned wlo) = w -> 0 <= w < 2 ^ 16 ->
  evt rsegs (op08_call Sp ops F fc gp tp m (data + off) (op08_take w rem)
               (FuzzIn (off + op08_take w rem) (rem - op08_take w rem)) 1 pf)
    (MS (mkR rz (Z_to_bv 64 Sp) gp tp e0 e1 e2 x8 (Z_to_bv 64 7) wlo whi q2 wpf q4 q5 q6 q7
             (Z_to_bv 64 0x39) w19 w20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) w22 w23
             (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) e3 e4 e5 e6)
        F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs)).
Proof.
  intros Sp ops F fc m rz gp tp e0 e1 e2 x8 wlo whi q2 wpf q4 q5 q6 q7 w19 w20 w22 w23 e3 e4 e5 e6
    off rem w pf Hr H19 H23 Hpf HW Hw.
  subst w19 w23 wpf.
  zstep. zstep.
  rewrite HW.
  if_cases K; zify_cond K.
  - assert (Kw : w < rem) by (rewrite ?Z.mod_small in K by lia; lia).
    assert (En : op08_take w rem = w) by (unfold op08_take; destruct (Z.ltb_spec w rem); lia).
    do 5 zstep.
    apply evt_done. unfold op08_call. cbn [fi_off fi_n]. rewrite En.
    do 14 eexists.
    replace (data + (off + w)) with (data + off + w) by lia.
    reflexivity.
  - assert (Kw : rem <= w) by (rewrite ?Z.mod_small in K by lia; lia).
    assert (En : op08_take w rem = rem) by (unfold op08_take; destruct (Z.ltb_spec w rem); lia).
    do 6 zstep.
    apply evt_done. unfold op08_call. cbn [fi_off fi_n]. rewrite En.
    do 14 eexists.
    replace (data + (off + rem)) with (data + off + rem) by lia.
    reflexivity.
Qed.

(* a byte of the input, as the code's lbu reads it and as at8 names it *)
Lemma op08_byte : forall m k, bytes_at rsegs m data D -> 0 <= k -> (Z.to_nat k < length D)%nat ->
  ov_read_bytes rsegs m (wa (data + k)) 1 = Some [nth (Z.to_nat k) D (b8 0)] /\
  0 <= bv_unsigned (nth (Z.to_nat k) D (b8 0)) < 256.
Proof.
  intros m k HD Hk Hl. split.
  - pose proof (bytes_at_read rsegs m data D k 1 HD Hk ltac:(lia)) as HR.
    rewrite disp_sub1 in HR by lia. exact HR.
  - pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) D (b8 0))) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* The facts the two case walks start from: llvm_case's state, its memory and the cursor after the op byte. *)
Ltac op08_open H :=
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 &
                 t3 & t4 & t5 & t6 & mm & j10 & j28 & EMS & HOPS & HN & HC & HC1 & HM);
  unfold MS in EMS; injection EMS; intros; subst;
  unfold llvm_mem in HM;
  destruct HM as (HMU0 & HWMO0 & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM
                  & HFN & HJ1 & HJ2 & HRW);
  unfold llvm_cursor, FUZZ_INPUT_MAX in HC;
  pose proof (bytes_at_bound rsegs _ data D HD) as HDB.

(* Case 0, 0x138f0 to receive's entry (fuzz_transport.c:1168-1171 `case 0: { const uint8_t *p;
   size_t n = fuzz_record(&in, &p); receive(p, n, 0, 0); }`): fuzz_record_m's u16 a byte at a time
   (s7 = the n before the op byte: 1, 2 or more), then the shared take and call at 0x13c64. *)
Lemma llvm_op0_call : forall m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro
    cA off n,
  llvm_case data D m0 gp tp 0 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (MS R F pc fc None m ro) ->
  fuzz_record_m D c1 = (cA, off, n) ->
  evt rsegs (op08_call Sp ops F fc gp tp m (data + off) n cA 0 0) (MS R F pc fc None m ro).
Proof.
  intros m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro cA off n H Hrec.
  op08_open H.
  (* the op byte's fuzz_u8 (the dispatch's c1): the cursor one byte on *)
  assert (EC1 : fst (fuzz_u8_m D c) = FuzzIn (fi_off c + 1) (fi_n c - 1)).
  { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  rewrite EC1 in *.
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb]. cbn [fi_off fi_n].
  (* ---- 0x138f0 beqz s6: the u16's low byte (fuzz.h:40-46), n == 0 after the op byte ---- *)
  zstep.
  if_cases K; zify_cond K.
  - (* n == 0: 0x13b3c mv s7, zero; mv a0, zero; mv a1, zero; j 0x13c64 (the u16 is 0, the take 0) *)
    assert (E1 : fi_n c - 1 = 0) by lia.
    assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) = (FuzzIn (fi_off c + 1) (fi_n c - 1), 0)).
    { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off]. rewrite E1. reflexivity. }
    rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
    do 4 zstep.
    eapply op0_join; [lia | reflexivity | f_equal; lia | vm_compute; reflexivity | lia].
  - (* n >= 1: 0x138f4 lbu a0, 1(s4) (the low byte); 0x138f8 li a1, 2; 0x138fc bne s7, a1 *)
    destruct (op08_byte _ (fi_off c + 1) HD ltac:(lia) ltac:(lia)) as [HR0 Hb0].
    set (b0 := nth (Z.to_nat (fi_off c + 1)) D (b8 0)) in *.
    do 3 zstep.
    if_cases K1; zify_cond K1.
    + (* n >= 2 after the op byte: 0x13c54 lbu a1, 2(s4) (the high byte); 0x13c58 s7 -= 3;
         0x13c5c s3 = s4 + 3; 0x13c60 slli a1, a1, 8 *)
      destruct (op08_byte _ (fi_off c + 2) HD ltac:(lia) ltac:(lia)) as [HR1 Hb1].
      set (b1 := nth (Z.to_nat (fi_off c + 2)) D (b8 0)) in *.
      assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) =
                   (FuzzIn (fi_off c + 3) (fi_n c - 3), bv_unsigned b0 + 256 * bv_unsigned b1)).
      { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off].
        destruct (Z.eqb_spec (fi_n c - 1) 0) as [E|E]; [lia|]. cbn [fi_n fi_off].
        destruct (Z.eqb_spec (fi_n c - 1 - 1) 0) as [E'|E']; [lia|].
        unfold at8, bz.
        replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
        replace (fi_off c + 2 + 1) with (fi_off c + 3) by lia.
        replace (fi_n c - 1 - 1 - 1) with (fi_n c - 3) by lia.
        fold b0 b1.
        rewrite lor_shiftl8_add by lia. rewrite Z.mod_small by lia. reflexivity. }
      rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
      do 4 zstep.
      assert (S8 : 0 <= Z.shiftl (bv_unsigned b1) 8 < 65536).
      { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. }
      eapply op0_join; [lia | f_equal; lia | f_equal; lia | | lia].
      rewrite !unsigned_lit by lia. rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
    + (* one byte after the op byte: 0x13900 mv s7, zero; mv a1, zero; s3 = s4 + 2; j 0x13c64 *)
      assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) =
                   (FuzzIn (fi_off c + 2) 0, bv_unsigned b0)).
      { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off].
        destruct (Z.eqb_spec (fi_n c - 1) 0) as [E|E]; [lia|]. cbn [fi_n fi_off].
        destruct (Z.eqb_spec (fi_n c - 1 - 1) 0) as [E'|E']; [|lia].
        unfold at8, bz. fold b0.
        replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
        replace (fi_n c - 1 - 1) with 0 by lia.
        rewrite ?Z.shiftl_0_l, ?Z.lor_0_r. rewrite Z.mod_small by lia. reflexivity. }
      rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
      do 4 zstep.
      eapply op0_join; [lia | f_equal; lia | reflexivity | | lia].
      rewrite !unsigned_lit by lia. rewrite Z.lor_0_l. reflexivity.
Qed.

(* Case 8, 0x13ac0 to receive's entry (fuzz_transport.c:1206-1211 `default: { uint8_t pf = fuzz_u8(&in);
   ... receive(p, n, 1, pf); }`): the flags byte (a3), then fuzz_record_m's u16 a byte at a time (s7 = the n
   before the op byte: 1, 2, 3 or more), then the shared take and call at 0x13f38. *)
Lemma llvm_op8_call : forall m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro
    c2 pf cA off n,
  llvm_case data D m0 gp tp 8 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (MS R F pc fc None m ro) ->
  fuzz_u8_m D c1 = (c2, pf) -> fuzz_record_m D c2 = (cA, off, n) ->
  evt rsegs (op08_call Sp ops F fc gp tp m (data + off) n cA 1 pf) (MS R F pc fc None m ro).
Proof.
  intros m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro c2 pf cA off n
    H Hpf Hrec.
  op08_open H.
  assert (EC1 : fst (fuzz_u8_m D c) = FuzzIn (fi_off c + 1) (fi_n c - 1)).
  { unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia|reflexivity]. }
  rewrite EC1 in *.
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb]. cbn [fi_off fi_n].
  (* ---- 0x13ac0 beqz s6: the flags byte (fuzz.h:40-46), n == 0 after the op byte ---- *)
  zstep.
  if_cases K; zify_cond K.
  - (* n == 0: 0x13b60 mv a3, zero; mv s7, zero; mv a0, zero; mv a1, zero; j 0x13f38 *)
    assert (E1 : fi_n c - 1 = 0) by lia.
    assert (EP : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) = (FuzzIn (fi_off c + 1) (fi_n c - 1), 0)).
    { unfold fuzz_u8_m. cbn [fi_n]. rewrite E1. reflexivity. }
    rewrite EP in Hpf. injection Hpf as <- <-.
    assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) = (FuzzIn (fi_off c + 1) (fi_n c - 1), 0)).
    { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off]. rewrite E1. reflexivity. }
    rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
    do 5 zstep.
    eapply op8_join; [lia | reflexivity | f_equal; lia | reflexivity | vm_compute; reflexivity | lia].
  - (* n >= 1: 0x13ac4 lbu a3, 1(s4) (the flags); 0x13ac8 li a0, 2; 0x13acc bne s7, a0 *)
    destruct (op08_byte _ (fi_off c + 1) HD ltac:(lia) ltac:(lia)) as [HR0 Hb0].
    set (bf := nth (Z.to_nat (fi_off c + 1)) D (b8 0)) in *.
    assert (EP : fuzz_u8_m D (FuzzIn (fi_off c + 1) (fi_n c - 1)) =
                 (FuzzIn (fi_off c + 2) (fi_n c - 2), bv_unsigned bf)).
    { unfold fuzz_u8_m. cbn [fi_n fi_off].
      destruct (Z.eqb_spec (fi_n c - 1) 0) as [E|E]; [lia|].
      unfold at8, bz. fold bf. f_equal. f_equal; lia. }
    rewrite EP in Hpf. injection Hpf as <- <-.
    do 3 zstep.
    if_cases K1; zify_cond K1.
    + (* n >= 2 after the op byte: 0x13ca4 lbu a0, 2(s4) (the u16's low byte); 0x13ca8 li a1, 3;
         0x13cac bne s7, a1 *)
      destruct (op08_byte _ (fi_off c + 2) HD ltac:(lia) ltac:(lia)) as [HR1 Hb1].
      set (bl := nth (Z.to_nat (fi_off c + 2)) D (b8 0)) in *.
      do 3 zstep.
      if_cases K2; zify_cond K2.
      * (* n >= 3 after the op byte: 0x13f28 lbu a1, 3(s4) (the high byte); 0x13f2c s7 -= 4;
           0x13f30 s3 = s4 + 4; 0x13f34 slli a1, a1, 8 *)
        destruct (op08_byte _ (fi_off c + 3) HD ltac:(lia) ltac:(lia)) as [HR2 Hb2].
        set (bh := nth (Z.to_nat (fi_off c + 3)) D (b8 0)) in *.
        assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 2) (fi_n c - 2)) =
                     (FuzzIn (fi_off c + 4) (fi_n c - 4), bv_unsigned bl + 256 * bv_unsigned bh)).
        { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off].
          destruct (Z.eqb_spec (fi_n c - 2) 0) as [E|E]; [lia|]. cbn [fi_n fi_off].
          destruct (Z.eqb_spec (fi_n c - 2 - 1) 0) as [E'|E']; [lia|].
          unfold at8, bz.
          replace (fi_off c + 2 + 1) with (fi_off c + 3) by lia.
          replace (fi_off c + 3 + 1) with (fi_off c + 4) by lia.
          replace (fi_n c - 2 - 1 - 1) with (fi_n c - 4) by lia.
          fold bl bh.
          rewrite lor_shiftl8_add by lia. rewrite Z.mod_small by lia. reflexivity. }
        rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
        do 4 zstep.
        assert (S8 : 0 <= Z.shiftl (bv_unsigned bh) 8 < 65536).
        { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. }
        eapply op8_join; [lia | f_equal; lia | f_equal; lia | reflexivity | | lia].
        rewrite !unsigned_lit by lia. rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
      * (* two bytes after the op byte: 0x13cb0 mv s7, zero; mv a1, zero; s3 = s4 + 3; j 0x13f38 *)
        assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 2) (fi_n c - 2)) =
                     (FuzzIn (fi_off c + 3) 0, bv_unsigned bl)).
        { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off].
          destruct (Z.eqb_spec (fi_n c - 2) 0) as [E|E]; [lia|]. cbn [fi_n fi_off].
          destruct (Z.eqb_spec (fi_n c - 2 - 1) 0) as [E'|E']; [|lia].
          unfold at8, bz. fold bl.
          replace (fi_off c + 2 + 1) with (fi_off c + 3) by lia.
          replace (fi_n c - 2 - 1) with 0 by lia.
          rewrite ?Z.shiftl_0_l, ?Z.lor_0_r. rewrite Z.mod_small by lia. reflexivity. }
        rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
        do 4 zstep.
        eapply op8_join; [lia | f_equal; lia | reflexivity | reflexivity | | lia].
        rewrite !unsigned_lit by lia. rewrite Z.lor_0_l. reflexivity.
    + (* one byte after the op byte (the flags): 0x13ad0 mv s7, zero; mv a0, zero; mv a1, zero;
         s3 = s4 + 2; j 0x13f38 *)
      assert (EU : fuzz_u16_m D (FuzzIn (fi_off c + 2) (fi_n c - 2)) = (FuzzIn (fi_off c + 2) 0, 0)).
      { unfold fuzz_u16_m, fuzz_u8_m. cbn [fi_n fi_off].
        replace (fi_n c - 2) with 0 by lia. reflexivity. }
      rewrite (op08_rec_u16 D _ _ _ _ EU) in Hrec. injection Hrec as <- <- <-.
      do 5 zstep.
      eapply op8_join; [lia | f_equal; lia | reflexivity | reflexivity | vm_compute; reflexivity | lia].
Qed.

(* 0x13f58 j 0x14288 (receive's return); 0x14288 mv s3, s0 (the cursor after the record); the latch 0x1428c *)
Lemma llvm_rcv_ret : forall m0 m tp Sp lo ops cA Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc j10 j28
    x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31,
  llvm_mem data D Sp lo Bw m0 m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  0 <= ops < OPS_MAX -> llvm_cursor D cA ->
  evt rsegs (llvm_latch data D m0 gp tp Sp lo ops cA Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 (Z_to_bv 64 (data + fi_off cA)) (Z_to_bv 64 7)
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x39) x19 x20 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
             (Z_to_bv 64 (fi_n cA)) x23 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
             (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13f58) fc None m (seg_rom rsegs)).
Proof.
  intros m0 m tp Sp lo ops cA Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc j10 j28
    x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31 HM HOPS HC.
  do 2 zstep.
  apply evt_done.
  unfold llvm_latch. do 22 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC|]. exact HM.
Qed.

End OP08E.

(* ---- the SR level ---- *)

(* the canonical register map of a register file equal to an explicit one off x0 *)
Lemma op08_mkR_of : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 regs,
  Regs6ss.xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                         x24 x25 x26 x27 x28 x29 x30 x31) regs ->
  Regs6ss.mkR_of regs = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                         x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 regs H.
  unfold Regs6ss.mkR_of. rewrite <- !H by reflexivity. reflexivity.
Qed.

(* a span of the input as bytes_at reads it *)
Lemma op08_bytes_sub : forall m a (bs : list byte) k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* what fuzz_record_m returns from a cursor inside the input *)
Lemma op08_rec_facts : forall D c cA off n, llvm_cursor D c -> fuzz_record_m D c = (cA, off, n) ->
  fi_off c <= off /\ 0 <= n <= 65535 /\ fi_off cA = off + n /\ off + n + fi_n cA = fi_off c + fi_n c /\
  llvm_cursor D cA.
Proof.
  intros D c cA off n HC H. unfold llvm_cursor in *. unfold fuzz_record_m in H.
  destruct (fuzz_u16_m D c) as [c1 w] eqn:EU.
  assert (H1 : fi_off c <= fi_off c1 /\ fi_off c1 + fi_n c1 = fi_off c + fi_n c /\ 0 <= fi_n c1 /\
               0 <= w < 2 ^ 16).
  { unfold fuzz_u16_m, fuzz_u8_m in EU.
    destruct (Z.eqb_spec (fi_n c) 0) as [E|E]; cbn [fi_n fi_off] in EU;
      [destruct (Z.eqb_spec (fi_n c) 0) as [E'|E']; [|lia]
      |destruct (Z.eqb_spec (fi_n c - 1) 0) as [E'|E']];
      injection EU as <- <-; cbn [fi_n fi_off];
      (split; [lia|]); (split; [lia|]); (split; [lia|]); apply Z.mod_pos_bound; lia. }
  unfold fuzz_take_m in H. injection H as <- <- <-. cbn [fi_off fi_n].
  destruct (Z.ltb_spec w (fi_n c1)); lia.
Qed.

(* mkR_of with every register read through getr *)
Lemma op08_mkR_of_getr : forall regs, Regs6ss.mkR_of regs =
  mkR (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 5)
      (YK11.getr regs 6) (YK11.getr regs 7) (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 10)
      (YK11.getr regs 11) (YK11.getr regs 12) (YK11.getr regs 13) (YK11.getr regs 14) (YK11.getr regs 15)
      (YK11.getr regs 16) (YK11.getr regs 17) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20)
      (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25)
      (YK11.getr regs 26) (YK11.getr regs 27) (YK11.getr regs 28) (YK11.getr regs 29) (YK11.getr regs 30)
      (YK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* a callee-saved register across a call, read off the register file before it *)
Lemma op08_pres : forall R regs' regs2 r, Regs6ss.xregs_eqv R regs' -> regs_preserved regs' regs2 ->
  callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr R (Z_to_bv 5 r).
Proof. intros R regs' regs2 r Hx Hp Hc. rewrite (Hp r Hc). apply sr_getr_eqv. exact Hx. Qed.

(* the loop's footprint LLVM_FP is the SR window and the world *)
Lemma op08_fp : forall Sp x, ~ outside (LLVM_FP Sp) x ->
  (LLVM_SR_S Sp - LLVM_SR_K <= x < LLVM_SR_S Sp) \/ h_world x.
Proof.
  intros Sp x NO. unfold LLVM_FP in NO. unfold LLVM_SR_S, LLVM_SR_K, h_world.
  destruct (Z_le_dec (Sp - LLVM_LOOP_K) x) as [H1|H1];
    [destruct (Z_lt_dec x (Sp + LLVM_FRAME)) as [H2|H2]; [left; lia|] |];
    (right; destruct (Z_le_dec W_BASE_PLAIN x), (Z_lt_dec x (W_BASE_PLAIN + W_LEN)); try lia;
     exfalso; apply NO; cbn [outside]; (split; [lia|]); (split; [lia | exact I])).
Qed.

Section OP08S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context (data : Z) (D : list byte).

(* The call of receive from the loop at sp = Sp (_sr.v llvm_sr_bar for build_and_receive, with receive's window
   receive_FRAME = 8240 <= LLVM_LOOP_K): from the SR config at its entry, with the loop's facts and receive's
   arguments, the continuation gets the heap frame a malloc returned, the model's world at it, the callee-saved
   registers, sr_fr, the budget and llvm_mem again. *)
Lemma llvm_sr_rec : forall Sp lo Bw (fx' : YK11.FPState) regs m0 mem md L A L0 A0 mem0 md0 b
    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    (p : Z) (bytes : list byte) (by_poll pf : Z) (P : config -> Prop),
  h_binds B API ->
  (forall fx'' : YK11.FPState, @receive_contract fx'' rc B API) ->
  sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md ->
  YM05.alloc_ceiling <= lo ->
  frm_zero (@fp_csr fx') ->
  res_ok_slots A b -> LLVMFuzzerTestOneInput_c.llvm_room b ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  llvm_mem data D Sp lo Bw m0 (normalize rsegs mem) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
  (exists q kq, In (q, kq) (user_blocks A0) /\ ptr_addr L0 q <= data /\
     data + Z.of_nat (length D) <= ptr_addr L0 q + kq) ->
  receive_args B L A regs mem Bw p bytes by_poll pf ->
  (forall (fx'' : YK11.FPState) regs' mem' md' L' A' a Bw',
     h_addr_ok a ->
     receive_m timg_plain Bw a bytes by_poll pf = Some (Bw', tt) ->
     regs_preserved regs regs' -> frm_zero (@fp_csr fx'') ->
     sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L' A' mem' md' -> res_ok_slots A' b ->
     llvm_mem data D Sp lo Bw' (normalize rsegs mem') (normalize rsegs mem')
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 ->
     SR rsegs (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 receive_ENTRY) mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros Sp lo Bw fx' regs m0 mem md L A L0 A0 mem0 md0 b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28
    p bytes by_poll pf P HB HREC FR Hlo Hfrm Hres Hroom Hsp Htp Hra HM HIN HARGS K.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  pose proof FR as (HMR & HW & HBd & HID & Hmd & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle & Hlen).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HJ1 & HJ2
                   & HRW).
  assert (HREL : mem_rel rsegs mem (normalize rsegs mem)) by exact (mem_rel_normalize rsegs mem MI).
  pose proof sr_ceiling as Hc.
  unfold LLVM_LOOP_K in HLO. unfold LLVM_FRAME in HSP2.
  assert (Hspz : spZ regs = Sp).
  { unfold spZ. rewrite Hsp. apply MState.unsigned_lit. unfold W_BASE_PLAIN, W_LEN in *. lia. }
  assert (HK0 : receive_FRAME = 8240) by reflexivity.
  (* the budget: the record is at most 65535 bytes (receive_args) *)
  pose proof HARGS as (_ & _ & _ & _ & _ & _ & Hlen65 & _).
  assert (Hrs : room_slots b (Z.max 1 (Z.of_nat (length bytes)))).
  { unfold LLVMFuzzerTestOneInput_c.llvm_room in Hroom. destruct Hroom as (R1 & R2 & R3).
    apply room_slots_small; lia. }
  (* h_pre at the call *)
  assert (HPRE : h_pre B API receive_FRAME L A regs mem md b Bw).
  { split.
    { apply (g_pre B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md regs receive_FRAME FR Hra);
        rewrite ?Hspz, ?HK0; unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME; try lia.
      exact Htp. }
    split; [exact HID|]. split; [exact Hh|]. split; [exact Hl|].
    split; [rewrite SEGS; exact MI|]. split; [exact Hres|].
    split; [unfold w_off_stack in HWOS |- *; rewrite Hsp, HK0; unfold LLVM_LOOP_K in HWOS; lia|].
    split; [exact (sr_wmem_back mem (normalize rsegs mem) Bw HREL HWM)|].
    split; [exact HFN|].
    exact (sr_relro_back mem (normalize rsegs mem) HREL HRO). }
  (* the call *)
  rewrite <- SEGS.
  eapply SR_bind.
  { exact (HREC fx' HB L A regs mem md b Bw p bytes by_poll pf HPRE Hfrm HARGS Hrs). }
  intros c2 (a & Bw' & Ha & Hca & Hnimg & HRM & Hpost).
  destruct Hpost as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hcpk & HID2 & Hh2 & Hl2 & Hblk2 & Hub2 &
                     Hlen2 & Hres2 & Hro2 & Hgk & HWM2 & HFN2 & HRO2).
  pose proof Hcpk as (HMR2 & HW2 & HB2 & Hle2 & Hstab & Hrp & Hvm & Hfr & Hkeep & Hscr).
  rewrite SEGS in Hro2.
  set (n := Z.max 1 (Z.of_nat (length bytes))) in *.
  assert (HElow : forall x, (h_world x \/ a <= x < a + n \/ ms_ctx B <= x < ms_ctx B + CTX_SIZE) ->
                    x < YM05.alloc_ceiling).
  { intros x [Hx|[Hx|Hx]]; [destruct (sr_world_img B SEGS WORLD x Hx) as [_ Hx2] | |]; lia. }
  assert (FR2 : sr_fr B API LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L2 A2 mem2 md2).
  { apply (sr_fr_call B API SEGS AX ERR WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A mem md
             receive_FRAME regs
             (fun x => h_world x \/ a <= x < a + n \/ ms_ctx B <= x < ms_ctx B + CTX_SIZE)
             L2 A2 regs2 mem2 md2 FR);
      rewrite ?Hspz, ?HK0; unfold LLVM_SR_S, LLVM_SR_K, LLVM_LOOP_K, LLVM_FRAME; try lia.
    - exact Hcpk.
    - intros x [Hx|[Hx|Hx]].
      + right. right. left. exact Hx.
      + right. left. split; [lia|]. pose proof (Hnimg (x - a) ltac:(lia)) as Hn.
        replace (a + (x - a)) with x in Hn by lia. exact Hn.
      + right. right. right. exact Hx.
    - intros x _. unfold h_world. lia.
    - intros x Hx Hw. exfalso. pose proof (HElow x Hx). lia.
    - intros p0 k Hpk. exact (Hub2 p0 k (proj1 (Hub p0 k Hpk))).
    - intros x k i Hin Hi. apply blocks_In in Hin as (p0 & Hp & Hpin).
      destruct (Hub p0 k Hpin) as [HpA Hpa].
      pose proof (Hkeep p0 k i HpA (Hub2 p0 k HpA) Hi) as E. rewrite Hpa, Hp in E. exact E.
    - exact HID2.
    - exact Hro2.
    - exact Hgk. }
  rewrite SEGS.
  apply (K fx2 regs2 mem2 md2 L2 A2 a Bw' Ha HRM Hrp Hfrm2 FR2 Hres2).
  rewrite SEGS in Hfr, Hkeep, Hscr.
  apply (llvm_mem_sr_call data D Sp lo receive_FRAME Bw Bw' m0 mem mem2); try assumption.
  - rewrite HK0. unfold LLVM_LOOP_K. lia.
  - intros x Hx. apply Hfr.
    + left. unfold LLVM_FRAME in Hx. lia.
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ x HMR Ho). lia.
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ x HMR2 Ho). lia.
    + unfold scratch_k. rewrite Hspz, HK0. unfold LLVM_FRAME in Hx. intros [Hs|Hs]; lia.
    + intros Hx2. pose proof (HElow x Hx2). unfold LLVM_FRAME in Hx. lia.
  - intros x Hx. apply Hscr. left. rewrite Hspz. exact Hx.
  - intros i Hi. destruct HIN as (q & kq & Hin & H1 & H2).
    destruct (Hub q kq Hin) as [HqA Hqa].
    pose proof (Hkeep q kq (data + i - ptr_addr L q) HqA (Hub2 q kq HqA) ltac:(rewrite Hqa; lia)) as E.
    replace (ptr_addr L q + (data + i - ptr_addr L q)) with (data + i) in E by lia. exact E.
Qed.

(* llvm_case_sr's own facts on the cursor *)
Lemma op08_case_facts : forall gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg,
  llvm_case_sr B API data D gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  fi_n c <> 0 /\ llvm_cursor D c /\ c1 = fst (fuzz_u8_m D c).
Proof.
  intros gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg H.
  destruct H as (fx' & regs & mem & md & L & A & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPe).
  destruct HPe as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & mm &
                   j10 & j28 & _ & _ & HN & HC & HC1 & _).
  split; [exact HN|]. split; [exact HC|]. exact HC1.
Qed.

(* A case that reads a record and calls receive (ops 0 and 8), at the SR level: from the case's SR config, the evt
   segment to receive's entry (g_run), the call (llvm_sr_rec), the evt segment from its return to the latch
   (g_run, which runs sr_run_norm). The continuation gets the heap frame a, receive_m's world at it, and the latch
   with the cursor after the record. *)
Lemma llvm_sr_rcv : forall gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg
    (P : config -> Prop) off n cA bp pf,
  h_binds B API ->
  (forall fx' : YK11.FPState, @receive_contract fx' rc B API) ->
  llvm_case_sr B API data D gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  (forall m0 F fc R pc m ro,
     llvm_case data D m0 gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
       (MS R F pc fc None m ro) ->
     evt rsegs (op08_call data Sp ops F fc gp tp m (data + off) n cA bp pf) (MS R F pc fc None m ro)) ->
  0 <= off -> 0 <= n <= 65535 -> off + n <= Z.of_nat (length D) -> llvm_cursor D cA ->
  - 2 ^ 31 <= bp < 2 ^ 31 -> 0 <= pf < 2 ^ 32 ->
  (forall a, h_addr_ok a -> receive_m timg_plain Bw a (sub D off (Z.to_nat n)) bp pf <> None) ->
  (forall a Bw' cfg', h_addr_ok a -> receive_m timg_plain Bw a (sub D off (Z.to_nat n)) bp pf = Some (Bw', tt) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cA Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp i Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P off n cA bp pf
    HB HREC HSR HEVT Hoff Hn Hon HCA Hbp Hpf HMOD K.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERR & CTX & WORLD & RELRO).
  destruct HSR as (fx' & regs & mem & md & L & A & -> & Hfrm & FR & Hc1 & Hc2 & Hres & Hroom & Htp & HIN & HPe).
  pose proof FR as (HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _).
  pose proof HPe as HPe'.
  destruct HPe' as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & mm &
                    j10 & j28 & EMS & HOPS & HN & HC & HC1 & HM).
  pose proof (ms_mem_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ EMS) as EM. subst mm.
  (* tp is the image's thread pointer (llvm_sr_at) *)
  assert (Etp : YK11.getr regs 4 = tp).
  { change (YK11.getr regs 4) with (getr (Regs6ss.mkR_of regs) 4).
    apply (f_equal (fun ms => getr (ms_regs ms) 4)) in EMS. exact EMS. }
  rewrite Etp in Htp.
  pose proof HM as HM1. unfold llvm_mem in HM1.
  destruct HM1 as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & _ & _ & _ & _ & _ & _ & _).
  unfold LLVM_FRAME in HSP2.
  assert (HSmax : LLVM_SR_S Sp <= 2 ^ 64) by (unfold LLVM_SR_S, LLVM_FRAME; lia).
  pose proof (bytes_at_bound rsegs _ data D HD) as HDB.
  unfold off_world in HOW.
  (* ---- the case's evt segment, to receive's entry ---- *)
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 fx' regs (Z_to_bv 64 (LLVM_CASE i))
            mem md L A (op08_call data Sp ops (@fp_regs fx') (@fp_csr fx') gp tp (normalize rsegs mem) (data + off) n cA
                          bp pf) P FR Hc1 HSmax).
  { exact (HEVT _ _ _ _ _ _ _ HPe). }
  { intros ms (u0 & u1 & u2 & u4 & u5 & u6 & u7 & u19 & u20 & u23 & u28 & u29 & u30 & u31 & ->).
    do 5 eexists. exists []. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x _ NO. exfalso. apply NO. exact I. }
  intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
  destruct HQ as (u0 & u1 & u2 & u4 & u5 & u6 & u7 & u19 & u20 & u23 & u28 & u29 & u30 & u31 & EQ).
  unfold MS in EQ. injection EQ; intros; subst R F pc' fc m0'.
  (* the registers at the call *)
  assert (G1 : YK11.getr regs' 1 = Z_to_bv 64 0x13f58) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G2 : YK11.getr regs' 2 = Z_to_bv 64 Sp) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G4 : YK11.getr regs' 4 = Z_to_bv 64 (ms_tp B)) by (rewrite (sr_getr_eqv _ _ _ Hx); exact Htp).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (data + off)) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G11 : YK11.getr regs' 11 = Z_to_bv 64 n) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G12 : YK11.getr regs' 12 = Z_to_bv 64 bp) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (G13 : YK11.getr regs' 13 = Z_to_bv 64 pf) by (rewrite (sr_getr_eqv _ _ _ Hx); reflexivity).
  assert (Hro' : ro_agree rsegs m') by exact (ro_agree_of_mem_rel rsegs _ _ Hrel).
  assert (HM' : llvm_mem data D Sp lo Bw (normalize rsegs m') (normalize rsegs m')
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28).
  { apply (llvm_mem_ext data D Sp lo Bw (normalize rsegs mem) (normalize rsegs mem) (normalize rsegs m'));
      [|exact HM].
    intros x. destruct Hrel as [E _]. symmetry. exact (E x). }
  set (bytes := sub D off (Z.to_nat n)).
  assert (Hlb : length bytes = Z.to_nat n) by (unfold bytes; apply length_sub; lia).
  (* ---- the call ---- *)
  apply (llvm_sr_rec Sp lo Bw (mkFP (@fp_regs fx') (@fp_csr fx')) regs' (normalize rsegs m') m' md L A L0 A0 mem0 md0
           b ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j10 j28 (data + off) bytes bp pf P HB HREC FR' Hc2 Hfrm Hres
           Hroom G2 G4).
  { rewrite G1. reflexivity. }
  { exact HM'. }
  { exact HIN. }
  { (* receive_args *)
    split; [exact G10|].
    split; [rewrite G11, Hlb, Z2Nat.id by lia; reflexivity|].
    split; [exact G12|]. split; [exact Hbp|].
    split; [rewrite G13, MState.unsigned_lit by lia; apply Z.mod_small; lia|]. split; [exact Hpf|].
    split; [rewrite Hlb, Z2Nat.id by lia; lia|].
    split.
    { apply (llvm_blk_norm B m' (data + off) bytes SEGS Hro').
      pose proof HM' as HM2. unfold llvm_mem in HM2.
      destruct HM2 as (_ & _ & HD' & _).
      pose proof (op08_bytes_sub _ data D (Z.to_nat off) (Z.to_nat n) HD' ltac:(lia)) as E.
      rewrite Z2Nat.id in E by lia. exact E. }
    split.
    { rewrite Hlb, Z2Nat.id by lia.
      apply (llvm_src_data B API data D LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 L A m' md (spZ regs')
               (data + off) n FR' HIN); [lia | lia |].
      unfold off_world. lia. }
    exact HMOD. }
  (* ---- after the call: back to the latch ---- *)
  intros fx2 regs2 mem2 md2 L2 A2 a Bw' Ha HRM Hrp Hfrm2 FR2 Hres2 HM2.
  rewrite G1.
  assert (E2 : YK11.getr regs2 2 = Z_to_bv 64 Sp)
    by exact (op08_pres _ _ _ 2 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E3 : YK11.getr regs2 3 = gp)
    by exact (op08_pres _ _ _ 3 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E4 : YK11.getr regs2 4 = tp)
    by exact (op08_pres _ _ _ 4 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E8 : YK11.getr regs2 8 = Z_to_bv 64 (data + fi_off cA))
    by exact (op08_pres _ _ _ 8 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E9 : YK11.getr regs2 9 = Z_to_bv 64 7)
    by exact (op08_pres _ _ _ 9 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E18 : YK11.getr regs2 18 = Z_to_bv 64 0x39)
    by exact (op08_pres _ _ _ 18 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E21 : YK11.getr regs2 21 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s))
    by exact (op08_pres _ _ _ 21 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E22 : YK11.getr regs2 22 = Z_to_bv 64 (fi_n cA))
    by exact (op08_pres _ _ _ 22 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E24 : YK11.getr regs2 24 = Z_to_bv 64 1)
    by exact (op08_pres _ _ _ 24 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E25 : YK11.getr regs2 25 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
    by exact (op08_pres _ _ _ 25 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E26 : YK11.getr regs2 26 = Z_to_bv 64 (W_BASE_PLAIN + OFF_M))
    by exact (op08_pres _ _ _ 26 Hx Hrp ltac:(unfold callee_saved; lia)).
  assert (E27 : YK11.getr regs2 27 = Z_to_bv 64 ops)
    by exact (op08_pres _ _ _ 27 Hx Hrp ltac:(unfold callee_saved; lia)).
  eapply (g_run B API SEGS AX HGG WORLD LLVM_SR_K (LLVM_SR_S Sp) L0 A0 mem0 md0 fx2 regs2 (Z_to_bv 64 0x13f58)
            mem2 md2 L2 A2
            (llvm_latch data D (normalize rsegs mem2) gp tp Sp lo ops cA Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (@fp_regs fx2) (@fp_csr fx2)) P FR2 Hc1 HSmax).
  { rewrite op08_mkR_of_getr. rewrite E2, E3, E4, E8, E9, E18, E21, E22, E24, E25, E26, E27.
    exact (llvm_rcv_ret data D _ _ tp Sp lo ops cA Bw' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ j10 j28
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2 HOPS HCA). }
  { intros ms HQ.
    destruct HQ as (rq & v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v8 & v20 & v23 &
                    v28 & v29 & v30 & v31 & m'' & k10 & k28 & -> & _ & _ & HMq).
    do 5 eexists. exists (LLVM_FP Sp). split; [reflexivity|].
    unfold llvm_mem in HMq. destruct HMq as (MUq & WMq & _).
    split; [exact MUq|]. split; [exact WMq|].
    intros x _ NO. destruct (op08_fp Sp x NO) as [Hw|Hw]; [left; exact Hw | right; left; exact Hw]. }
  intros R3 F3 pc3 fc3 m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  pose proof HQ as HQ'.
  destruct HQ' as (rq & v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v8 & v20 & v23 &
                   v28 & v29 & v30 & v31 & m'' & k10 & k28 & EQ3 & _ & _ & _).
  unfold MS in EQ3. injection EQ3; intros; subst R3 F3 pc3 fc3 m0''.
  apply (K a Bw' _ Ha HRM).
  exists (mkFP (@fp_regs fx2) (@fp_csr fx2)), regs3, m3, md2, L2, A2.
  split; [reflexivity|].
  split; [exact Hfrm2|].
  split; [exact FR3|].
  split; [exact Hc1|]. split; [exact Hc2|].
  split; [exact Hres2|]. split; [exact Hroom|].
  split; [rewrite (sr_getr_eqv _ _ _ Hx3); exact Htp|].
  split; [exact HIN|].
  rewrite (op08_mkR_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx3).
  eapply llvm_latch_ext; [|exact HQ].
  intros x. symmetry. exact (proj1 Hrel3 x).
Qed.

(* the cursor after the op byte, inside the input *)
Lemma op08_c1 : forall c c1 opb, llvm_cursor D c -> fi_n c <> 0 -> fuzz_u8_m D c = (c1, opb) ->
  llvm_cursor D c1 /\ fi_off c1 = fi_off c + 1.
Proof.
  intros c c1 opb HC HN E. unfold fuzz_u8_m in E.
  destruct (Z.eqb_spec (fi_n c) 0) as [Z0|Z0]; [lia|].
  injection E as <- _. unfold llvm_cursor in *. cbn [fi_off fi_n]. split; [lia | reflexivity].
Qed.

(* Case 0 of the op loop (fuzz_transport.c:1168-1171; TOps.v's op =? 0 branch): from the case's SR config, for an
   op byte with op = 0, the model's op not None at every heap frame receive's malloc may return, and a
   continuation from the latch after the op, the run reaches P. *)
Lemma llvm_op0_sr : forall gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b
    (A : nat -> Z) (k : nat) cfg (P : config -> Prop),
  h_binds B API ->
  (forall fx' : YK11.FPState, @receive_contract fx' rc B API) ->
  llvm_case_sr B API data D gp tp 0 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  snd (fuzz_u8_m D c) mod 9 = 0 ->
  (forall a, h_addr_ok a -> LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k <> None) ->
  (forall a Bres cout k1 cfg', h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, k1)) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b A k cfg P
    HB HREC HSR Hop HMOD K.
  destruct (op08_case_facts gp tp 0 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg HSR)
    as (HN & HC & HC1).
  destruct (fuzz_u8_m D c) as [cu opb] eqn:EU8.
  rewrite ?EU8 in HC1, Hop. cbn [fst snd] in HC1, Hop. subst cu.
  destruct (op08_c1 c c1 opb HC HN EU8) as [HC1' Ho1].
  destruct (fuzz_record_m D c1) as [[cA off] n] eqn:ER.
  destruct (op08_rec_facts D c1 cA off n HC1' ER) as (Hoff & Hn & HoA & HsA & HCA).
  (* the model's op 0 at A k = a: fuzz_record_m, then receive_m (p, n, 0, 0) at a *)
  assert (EOP : forall a, LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k =
            match receive_m timg_plain Bw a (sub D off (Z.to_nat n)) 0 0 with
            | Some (B1, _) => Some (B1, (cA, S k)) | None => None end).
  { intros a. unfold LLVMFuzzerTestOneInput_op_m. rewrite EU8. cbv beta iota zeta. rewrite Hop.
    cbn [Z.eqb]. rewrite ER. cbv beta iota zeta. rewrite aupd_at. reflexivity. }
  unfold llvm_cursor in HC1', HCA.
  apply (llvm_sr_rcv gp tp 0 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P
           off n cA 0 0 HB HREC HSR).
  - intros m0 F fc R pc m ro H.
    exact (llvm_op0_call data D m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro
             cA off n H ER).
  - lia.
  - exact Hn.
  - lia.
  - unfold llvm_cursor. lia.
  - lia.
  - lia.
  - intros a Ha Hnone. apply (HMOD a Ha). rewrite EOP, Hnone. reflexivity.
  - intros a Bw' cfg' Ha HRM HL. apply (K a Bw' cA (S k) cfg' Ha); [rewrite EOP, HRM; reflexivity | exact HL].
Qed.

(* Case 8, the switch's default (fuzz_transport.c:1206-1211; TOps.v's last branch): the same, with the flags byte
   read before the record and receive(p, n, 1, pf). *)
Lemma llvm_op8_sr : forall gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b
    (A : nat -> Z) (k : nat) cfg (P : config -> Prop),
  h_binds B API ->
  (forall fx' : YK11.FPState, @receive_contract fx' rc B API) ->
  llvm_case_sr B API data D gp tp 8 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  snd (fuzz_u8_m D c) mod 9 = 8 ->
  (forall a, h_addr_ok a -> LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k <> None) ->
  (forall a Bres cout k1 cfg', h_addr_ok a ->
     LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k = Some (Bres, (cout, k1)) ->
     llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b A k cfg P
    HB HREC HSR Hop HMOD K.
  destruct (op08_case_facts gp tp 8 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg HSR)
    as (HN & HC & HC1).
  destruct (fuzz_u8_m D c) as [cu opb] eqn:EU8.
  rewrite ?EU8 in HC1, Hop. cbn [fst snd] in HC1, Hop. subst cu.
  destruct (op08_c1 c c1 opb HC HN EU8) as [HC1' Ho1].
  (* the flags byte (fuzz_u8_m, fuzz.h:40-46) *)
  destruct (fuzz_u8_m D c1) as [c2 pf] eqn:EP.
  assert (HC2 : llvm_cursor D c2 /\ fi_off c1 <= fi_off c2 /\ 0 <= pf < 256).
  { unfold fuzz_u8_m in EP. unfold llvm_cursor in *.
    destruct (Z.eqb_spec (fi_n c1) 0) as [E|E]; injection EP as <- <-; cbn [fi_off fi_n];
      [lia|].
    split; [lia|]. split; [lia|]. unfold at8, bz.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (fi_off c1)) D (b8 0))) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 8) with 256 in R. lia. }
  destruct HC2 as (HC2 & Ho2 & Hpf).
  destruct (fuzz_record_m D c2) as [[cA off] n] eqn:ER.
  destruct (op08_rec_facts D c2 cA off n HC2 ER) as (Hoff & Hn & HoA & HsA & HCA).
  (* the model's op 8 at A k = a: the flags byte, fuzz_record_m, then receive_m (p, n, 1, pf) at a *)
  assert (EOP : forall a, LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd A k a) D c k =
            match receive_m timg_plain Bw a (sub D off (Z.to_nat n)) 1 pf with
            | Some (B1, _) => Some (B1, (cA, S k)) | None => None end).
  { intros a. unfold LLVMFuzzerTestOneInput_op_m. rewrite EU8. cbv beta iota zeta. rewrite Hop.
    cbn [Z.eqb Pos.eqb]. rewrite EP. cbv beta iota zeta. rewrite ER. cbv beta iota zeta. rewrite aupd_at.
    reflexivity. }
  unfold llvm_cursor in HC1', HC2, HCA.
  apply (llvm_sr_rcv gp tp 8 Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P
           off n cA 1 pf HB HREC HSR).
  - intros m0 F fc R pc m ro H.
    exact (llvm_op8_call data D m0 gp tp Sp lo ops c c1 Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R pc m ro
             c2 pf cA off n H EP ER).
  - lia.
  - exact Hn.
  - lia.
  - unfold llvm_cursor. lia.
  - lia.
  - lia.
  - intros a Ha Hnone. apply (HMOD a Ha). rewrite EOP, Hnone. reflexivity.
  - intros a Bw' cfg' Ha HRM HL. apply (K a Bw' cA (S k) cfg' Ha); [rewrite EOP, HRM; reflexivity | exact HL].
Qed.

End OP08S.
