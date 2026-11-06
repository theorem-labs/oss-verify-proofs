(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x1427c .. 0x142e8 (fuzz/fuzz_transport.c:1096):
   sys = spec_system_at(c.bytes, c.len) >= 0, inlined. len < 4 gives sys = 0 (0x142e4); else the loop
   0x14290-0x142d4 scans i = 0 .. len - 4 for F0 13 xx 70 in the struct at sp+0x60 (its UBSan checks compare i with
   sp+0x38 = -(sp + 0x60) and sp+0x30 = ~(sp + 0x60): never hit). The scan is DgnSpec's system_at of the struct's first
   len bytes (t4_sys_val); the loop is proved by induction on the turns left, with the invariant that no index below
   the counter is a hit. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_s.
Import ListNotations.
Open Scope Z_scope.

(* the 40 bytes at sp+0x60: the struct and the 8 free bytes after it *)
Definition t4_J (B1 D : list byte) (c3 : fuzz_in) (display key : Z) (jhi : list byte) : list byte :=
  t4_cs B1 D c3 display key ++ jhi.

(* one byte of a block, read at a variable offset *)
Lemma t4_rdJ : forall m A (J : list byte) k (kn : nat), bytes_at rsegs m A J -> Z.of_nat kn = k ->
  (kn < length J)%nat -> ov_read_bytes rsegs m (wa (A + k)) 1 = Some [nth kn J (b8 0)].
Proof.
  intros m A J k kn HB Hk Hn. subst k.
  rewrite (bytes_at_read rsegs m A J (Z.of_nat kn) 1 HB) by lia.
  rewrite Nat2Z.id. rewrite t4_sub1 by lia. reflexivity.
Qed.

Lemma t4_J24 : forall B1 D c3 display key jhi, llvm_cursor D c3 ->
  nth 24 (t4_J B1 D c3 display key jhi) (b8 0) = b8 (t4_len D c3).
Proof.
  intros B1 D c3 display key jhi HC. pose proof (t4_cbD D c3 HC) as (H1 & H2 & H3).
  pose proof (t4_cb_len B1 D c3 H1 H2 H3) as L.
  unfold t4_J, t4_cs, cmd_struct. rewrite <- !app_assoc.
  rewrite app_nth2 by (rewrite L; lia). rewrite L. reflexivity.
Qed.

Lemma t4_bu8 : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x H. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact H.
Qed.

Lemma t4_sys3 : forall B1 D c3, t4_len D c3 = 3 -> length (t4_cb B1 D c3) = 24%nat -> t4_sys B1 D c3 = false.
Proof.
  intros B1 D c3 HL LCB. unfold t4_sys. rewrite HL. unfold system_at.
  rewrite firstn_length, LCB. reflexivity.
Qed.

Lemma t4_ex_true : forall (f : nat -> bool) k i, (i < k)%nat -> f i = true -> existsb f (seq 0 k) = true.
Proof. intros f k i Hi Hf. apply existsb_exists. exists i. split; [apply in_seq; lia | exact Hf]. Qed.

Lemma t4_lxor63 : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof. intros x H. change 9223372036854775808 with (2 ^ 63). apply zb_lxor_pow2_small; lia. Qed.

(* s10 = (a0 >= 0) after `slti a0, a0, 0; xori s10, a0, 1` *)
Ltac t4_s10 :=
  first [ reflexivity
        | (f_equal; rewrite ?t4_lxor63 by lia; decide_tests; reflexivity)
        | (idtac "S10FAIL"; t4_goal; fail 1) ].

Lemma t4_C : forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms (Q : machine_state -> Prop),
  t4_SB data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
  (forall ms', t4_SC data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms Q H HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jio & jhi & -> &
                 E0 & E1 & E2 & E3 & E4 & E5 & E6 & E8 & E9 & E10 & E11 & HOK & LJHI & HM).
  subst s0 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & _ & _ & _ & _ & _ & _ & _).
  pose proof (t4_mem_j60 _ _ _ _ _ _ _ _ _ _ _ HM) as HJ.
  change (t4_cs B1 D c3 display key ++ jhi) with (t4_J B1 D c3 display key jhi) in HJ.
  pose proof (t4_len_rng D c3) as HLEN.
  pose proof (t4_cbD D c3 HCUR) as (HCB1 & HCB2 & HCB3).
  pose proof (t4_cb_len B1 D c3 HCB1 HCB2 HCB3) as LCB.
  assert (LJ : length (t4_J B1 D c3 display key jhi) = 40%nat) by (apply t4_cs_jhi_len; assumption).
  pose proof (t4_mem_rd8 _ _ _ _ _ _ _ _ _ _ _ 56%nat (Z_to_bv 64 (2 ^ 64 - (Sp + 96))) (Sp + 56) HM
                ltac:(unfold llvm_frame, llvm_saved; cells_cbv; reflexivity) ltac:(lia)) as HR56.
  pose proof (t4_mem_rd8 _ _ _ _ _ _ _ _ _ _ _ 48%nat (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96))) (Sp + 48) HM
                ltac:(unfold llvm_frame, llvm_saved; cells_cbv; reflexivity) ltac:(lia)) as HR48.
  assert (SYSV : existsb (sys_hit (t4_J B1 D c3 display key jhi)) (seq 0 (Z.to_nat (t4_len D c3) - 3))
                 = t4_sys B1 D c3).
  { unfold t4_J, t4_cs, cmd_struct. rewrite <- app_assoc. apply t4_sys_val; [exact LCB | exact HLEN]. }
  (* ---- the exit 0x142e8, s10 = sys ---- *)
  assert (EXIT : forall x0 x1 x2 x3 x4 x10 : word, x10 = Z_to_bv 64 (Z.b2z (t4_sys B1 D c3)) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                         (Z_to_bv 64 (g_ncmd B1)) (Z_to_bv 64 240) x0 x1 x2 x3 x4 a5 a6 a7
                         (Z_to_bv 64 (229576 + g_ncmd B1 * 40)) (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                         (Z_to_bv 64 19) (Z_to_bv 64 229576) (Z_to_bv 64 (t4_n D c3)) s7
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                         x10 (Z_to_bv 64 ops) t3 t4 t5 t6) F (Z_to_bv 64 0x142e8) fc None m (seg_rom rsegs))).
  { intros x0 x1 x2 x3 x4 x10 Ex10. apply HK. unfold t4_SC.
    do 28 eexists. exists m, jio, jhi.
    split; [reflexivity|].
    do 7 (split; [t4_weq|]). split; [exact Ex10|]. split; [t4_weq|].
    split; [exact HOK|]. split; [exact LJHI|]. exact HM. }
  (* ---- the scan loop 0x14290, i bytes looked at ---- *)
  assert (LOOP : forall (r : nat) (i : Z) (x0 x1 x2 x3 x4 : word),
    Z.of_nat r = t4_len D c3 - 3 - i -> 0 <= i < t4_len D c3 - 3 ->
    existsb (sys_hit (t4_J B1 D c3 display key jhi)) (seq 0 (Z.to_nat i)) = false ->
    x0 = Z_to_bv 64 i -> x1 = Z_to_bv 64 (t4_len D c3 - 3) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                         (Z_to_bv 64 (g_ncmd B1)) (Z_to_bv 64 240) x0 x1 x2 x3 x4 a5 a6 a7
                         (Z_to_bv 64 (229576 + g_ncmd B1 * 40)) (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                         (Z_to_bv 64 19) (Z_to_bv 64 229576) (Z_to_bv 64 (t4_n D c3)) s7
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                         (Z_to_bv 64 (Sp + 97)) (Z_to_bv 64 ops) t3 t4 t5 t6) F (Z_to_bv 64 0x14290) fc None m
                    (seg_rom rsegs))).
  { induction r as [|r IH]; intros i x0 x1 x2 x3 x4 Hr Hi Hpre E0 E1; [lia|]. subst x0 x1.
    pose proof (t4_rdJ m (Sp + 96) _ i (Z.to_nat i) HJ ltac:(lia) ltac:(lia)) as HRa.
    pose proof (t4_rdJ m (Sp + 96) _ (i + 1) (S (Z.to_nat i)) HJ ltac:(lia) ltac:(lia)) as HRb.
    pose proof (t4_rdJ m (Sp + 96) _ (i + 3) (S (S (S (Z.to_nat i)))) HJ ltac:(lia) ltac:(lia)) as HRc.
    pose proof (t4_byte_rng (nth (Z.to_nat i) (t4_J B1 D c3 display key jhi) (b8 0))) as RGa.
    pose proof (t4_byte_rng (nth (S (Z.to_nat i)) (t4_J B1 D c3 display key jhi) (b8 0))) as RGb.
    pose proof (t4_byte_rng (nth (S (S (S (Z.to_nat i)))) (t4_J B1 D c3 display key jhi) (b8 0))) as RGc.
    (* the end of a turn, 0x142cc: i + 1, and the loop test *)
    assert (NEXT : sys_hit (t4_J B1 D c3 display key jhi) (Z.to_nat i) = false -> forall y2 y3 y4 : word,
      evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                           (Z_to_bv 64 (g_ncmd B1)) (Z_to_bv 64 240) (Z_to_bv 64 i)
                           (Z_to_bv 64 (t4_len D c3 - 3)) y2 y3 y4 a5 a6 a7
                           (Z_to_bv 64 (229576 + g_ncmd B1 * 40)) (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                           (Z_to_bv 64 19) (Z_to_bv 64 229576) (Z_to_bv 64 (t4_n D c3)) s7
                           (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                           (Z_to_bv 64 (Sp + 97)) (Z_to_bv 64 ops) t3 t4 t5 t6) F (Z_to_bv 64 0x142cc) fc None m
                      (seg_rom rsegs))).
    { intros HNH y2 y3 y4.
      (* 0x142cc addi a0, a0, 1; 0x142d0 bne a1, a0 *)
      zstep. zstep.
      destruct (Z.eq_dec (i + 1) (t4_len D c3 - 3)) as [Ei|Ei].
      - (* the scan ends: 0x142d4 li a0, -1; 0x142d8 slti a0, a0, 0; 0x142dc xori s10, a0, 1; 0x142e0 j *)
        t4_br. do 4 zstep.
        apply EXIT.
        assert (SF : t4_sys B1 D c3 = false).
        { rewrite <- SYSV. replace (Z.to_nat (t4_len D c3) - 3)%nat with (S (Z.to_nat i)) by lia.
          rewrite t4_sys_step, Hpre, HNH. reflexivity. }
        rewrite SF. t4_s10.
      - t4_br.
        apply (IH (i + 1)); [lia | lia | | t4_weq | t4_weq].
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        rewrite t4_sys_step, Hpre, HNH. reflexivity. }
    (* 0x14290 ld a2, 0x38(sp); 0x14294 beq a2, a0 (trap) *)
    zstep. zstep. t4_br.
    (* 0x14298 add a2, s10, a0; 0x1429c lbu a3, -1(a2); 0x142a0 bne a3, s1 *)
    zstep. zstep. zstep.
    destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat i) (t4_J B1 D c3 display key jhi) (b8 0))) 240) as [Ha|Ha].
    2: { t4_br. eapply NEXT. unfold sys_hit, at8, bz. rewrite (proj2 (Z.eqb_neq _ _) Ha). reflexivity. }
    t4_br.
    (* 0x142a4 ld a3, 0x30(sp); 0x142a8 bgeu a0, a3 (trap) *)
    zstep. zstep. t4_br.
    (* 0x142ac lbu a3, 0(a2); 0x142b0 bne a3, s4 *)
    zstep. zstep.
    destruct (Z.eq_dec (bv_unsigned (nth (S (Z.to_nat i)) (t4_J B1 D c3 display key jhi) (b8 0))) 19) as [Hb|Hb].
    2: { t4_br. eapply NEXT. unfold sys_hit, at8, bz.
         rewrite (proj2 (Z.eqb_eq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hb). reflexivity. }
    t4_br.
    (* 0x142b4 addi a3, a0, 3; 0x142b8 ld a4, 0x30(sp); 0x142bc bltu a4, a3 (trap) *)
    zstep. zstep. zstep. t4_br.
    (* 0x142c0 lbu a2, 2(a2); 0x142c4 li a3, 0x70; 0x142c8 beq a2, a3 *)
    zstep. zstep. zstep.
    destruct (Z.eq_dec (bv_unsigned (nth (S (S (S (Z.to_nat i)))) (t4_J B1 D c3 display key jhi) (b8 0))) 112)
      as [Hc|Hc].
    - (* found: 0x142d8 slti a0, a0, 0; 0x142dc xori s10, a0, 1; 0x142e0 j 0x142e8 *)
      t4_br. do 3 zstep.
      apply EXIT.
      assert (ST : t4_sys B1 D c3 = true).
      { rewrite <- SYSV. apply (t4_ex_true _ _ (Z.to_nat i)); [lia|].
        unfold sys_hit, at8, bz.
        rewrite (proj2 (Z.eqb_eq _ _) Ha), (proj2 (Z.eqb_eq _ _) Hb), (proj2 (Z.eqb_eq _ _) Hc). reflexivity. }
      rewrite ST. t4_s10.
    - t4_br. eapply NEXT. unfold sys_hit, at8, bz.
      rewrite (proj2 (Z.eqb_eq _ _) Ha), (proj2 (Z.eqb_eq _ _) Hb), (proj2 (Z.eqb_neq _ _) Hc). reflexivity. }
  (* ---- 0x1427c lbu a1, 0x78(sp) (len); 0x14280 li a0, 4; 0x14284 bltu a1, a0 ---- *)
  pose proof (t4_rdJ m (Sp + 96) _ 24 24%nat HJ eq_refl ltac:(lia)) as HR24.
  rewrite (t4_J24 B1 D c3 display key jhi HCUR) in HR24.
  replace (Sp + 96 + 24) with (Sp + 120) in HR24 by lia.
  assert (HBL1 : bv_unsigned (b8 (t4_len D c3)) = t4_len D c3) by (apply t4_bu8; lia).
  zstep. rewrite ?HBL1. clear HR24.
  zstep. zstep.
  destruct (Z.lt_ge_cases (t4_len D c3) 4) as [L3|L4].
  - (* len = 3: 0x142e4 mv s10, zero *)
    t4_br. zstep.
    apply EXIT. rewrite (t4_sys3 B1 D c3 ltac:(lia) LCB). t4_weq.
  - (* 0x14288 mv a0, zero; 0x1428c addi a1, a1, -3 *)
    t4_br. zstep. zstep.
    apply (LOOP (Z.to_nat (t4_len D c3 - 3)) 0); [lia | lia | reflexivity | t4_weq | t4_weq].
Qed.
