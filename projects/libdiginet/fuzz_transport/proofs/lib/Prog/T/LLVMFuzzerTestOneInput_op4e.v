(* Case 4 of the op loop, the entry segment 0x13910 -> 0x13df4 (op4_entry_stmt of _op4k.v). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k.
Import ListNotations.
Open Scope Z_scope.

Section OP4E.
Context (data : Z) (D : list byte).

(* the four 8-byte zero stores of the struct (0x13950-0x1395c) as its 32 zero bytes *)
Lemma o4e_zeros32 : le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ []
  = repeat (b8 0) 32.
Proof. apply bytes_eq_of_zs. vm_compute. reflexivity. Qed.

(* lw of s->queued (0x13918, s5 + 0x46e0 = W_BASE_PLAIN + A_S_queued) is the signed 32-bit S_queued *)
Lemma o4e_sq : forall B, s32_at B 19792 = bv_swrap 32 (S_queued B).
Proof. intros B. unfold S_queued, A_S_queued, OFF_g_s. reflexivity. Qed.

(* 0x13960 (`beqz s6`): op_begin done (world B1), (int)s->queued at sp+0x28 (0x1391c), the struct c at sp+0x50
   zero (0x13950-0x1395c); the registers are llvm_case's. *)
Definition o4e_p60 (m0 : word -> option byte) (gp tp : word) (Sp lo ops : Z) (c c1 : fuzz_in) (B B1 : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (rr t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r8 t3 t4 t5 t6 : word)
         (m : word -> option byte) (j10 j30 j70 : list byte),
    ms = MS (mkR rr (Z_to_bv 64 Sp) gp tp t0 t1 t2 r8 (Z_to_bv 64 7) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x39) (Z_to_bv 64 (data + fi_off c1)) (Z_to_bv 64 (data + fi_off c))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) (Z_to_bv 64 (fi_n c1)) (Z_to_bv 64 (fi_n c))
                 (Z_to_bv 64 1) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_fail_next))
                 (Z_to_bv 64 (W_BASE_PLAIN + OFF_M)) (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x13960) fc None m (seg_rom rsegs) /\
    0 <= ops < OPS_MAX /\ fi_n c <> 0 /\ llvm_cursor D c /\ c1 = fst (fuzz_u8_m D c) /\
    op4_mem data D Sp lo B1 m0 m
      (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 (S_queued B))) j30 (repeat (b8 0) 32) j70
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* 0x13910 -> 0x13960: before = s->queued saved, op_begin, the struct zeroed *)
Lemma o4e_pre : forall Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    memset_contract ->
    llvm_case data D m0 gp tp 4 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    op_begin_m B = Some (B1, tt) ->
    (forall ms', o4e_p60 m0 gp tp Sp lo ops c c1 B B1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
                 evt rsegs Q ms') ->
    evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q MSC H HB1 HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 &
                 m & j10 & j28 & -> & HOPS & HN & HC & HC1 & HM).
  apply op4_of_llvm in HM.
  pose proof HM as HM0.
  unfold op4_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : Z.of_nat (length B) = W_LEN) by (rewrite LB, Z2Nat.id; [reflexivity | unfold W_LEN; lia]).
  unfold LLVM_CASE. cbn [Z.eqb Pos.eqb].
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_OW. wk_eq_fact OFF_GOT.
  wk_eq_fact OFF_M. wk_eq_fact OFF_g_s. wk_eq_fact A_S_queued.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* 0x13910-0x1391c: a0 = s->queued (lw), sd a0, 0x28(sp) *)
  do 4 zstep.
  assert (HM1 : op4_mem data D Sp lo B m0 m1
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
     CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
     C8 (Z_to_bv 64 (s32_at B 19792)); CB 72 (skipn 8 j28);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (op4_mem_after data D Sp lo 0 B B m0 m m1); [exact HM0 | unfold LLVM_LOOP_K; lia | exact MU | exact WMO
      | exact HMI | exact HSTK | exact HWM | exact HFN | exact HRW | reflexivity]. }
  clear HM0 MU WMO HMI HSTK HWM HFN HRW HD HRO.
  (* 0x13920-0x1392c: memset(&OW, 0, 0x130) (op_begin, fuzz_transport.c:390) *)
  pose proof HM1 as HM1c. unfold op4_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HWM & HFN & _ & _).
  do 4 zstep.
  assert (CW1 : rw_cells rsegs m1 (W_BASE_PLAIN + OFF_OW) [CB (Z.to_nat 304) (sub B OFF_OW 304)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m1 B OFF_OW 304 (W_BASE_PLAIN + OFF_OW) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub B OFF_OW 304).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) by lia. exact CW1.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m2 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 344) with (W_BASE_PLAIN + OFF_OW) in MU1, CZ1 by lia.
  cbn [Z.to_nat] in CZ1.
  assert (HM2 : op4_mem data D Sp lo (upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) m0 m2
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
     CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
     C8 (Z_to_bv 64 (s32_at B 19792)); CB 72 (skipn 8 j28);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (op4_mem_after_fill data D Sp lo B m0 m1 m2 OFF_OW 304);
      [ exact HM1 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_OW in *; lia).
    exact HFN. }
  clear HM1 HMI HWM HFN CW1 CZ1 MU1 WMO1 MI1.
  set (Ba := upd B OFF_OW (repeat (Z_to_bv 8 0) 304)) in *.
  assert (LBa : Z.of_nat (length Ba) = W_LEN)
    by (unfold Ba; rewrite length_upd; [exact LBz | lia | rewrite repeat_length; lia]).
  (* 0x13930-0x1393c: memset(&GOT, 0, 0xe0) (op_begin, fuzz_transport.c:391) *)
  pose proof HM2 as HM2c. unfold op4_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HWM & HFN & _ & _).
  rewrite (ret_pc_even 0x13930) by (first [lia | reflexivity]).
  do 4 zstep.
  assert (CW2 : rw_cells rsegs m2 (W_BASE_PLAIN + OFF_GOT) [CB (Z.to_nat 224) (sub Ba OFF_GOT 224)]).
  { pose proof (wm_cell rsegs W_BASE_PLAIN m2 Ba OFF_GOT 224 (W_BASE_PLAIN + OFF_GOT) HWM eq_refl
                  ltac:(lia) ltac:(lia)) as P.
    rewrite length_sub in P by lia. exact P. }
  eapply evt_cut.
  { eapply MSC with (junk := sub Ba OFF_GOT 224).
    - rewrite !unsigned_lit by lia.
      replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) by lia. exact CW2.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 &
                     -> & MU2 & WMO2 & MI2 & CZ2).
  rewrite !unsigned_lit in MU2, CZ2 by lia.
  replace (W_BASE_PLAIN + OFF_g_fail_next + 116) with (W_BASE_PLAIN + OFF_GOT) in MU2, CZ2 by lia.
  assert (HM3 : op4_mem data D Sp lo (upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) m0 m3
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
     CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
     C8 (Z_to_bv 64 (s32_at B 19792)); CB 72 (skipn 8 j28);
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (op4_mem_after_fill data D Sp lo Ba m0 m2 m3 OFF_GOT 224);
      [ exact HM2 | exact MU2 | exact WMO2 | exact MI2 | exact CZ2 | lia | lia | lia | ].
    unfold g_fail_next.
    rewrite u_at_upd_out by (rewrite ?repeat_length; unfold OFF_g_fail_next, OFF_GOT in *; lia).
    exact HFN. }
  clear HM2 HMI HWM HFN CW2 CZ2 MU2 WMO2 MI2.
  set (Bb := upd Ba OFF_GOT (repeat (Z_to_bv 8 0) 224)) in *.
  assert (LBb : Z.of_nat (length Bb) = W_LEN)
    by (unfold Bb; rewrite length_upd; [exact LBa | lia | rewrite repeat_length; lia]).
  (* 0x13940-0x1395c: OW.desk_off = -1, M.fail = g_fail_next (op_begin :392-393), the struct c zeroed *)
  pose proof HM3 as HM3c. unfold op4_mem in HM3c.
  destruct HM3c as (_ & _ & HD & _ & HSTK & _ & _ & _ & _ & _ & _ & HMI & _ & HWM & HFN & HRW & _).
  rewrite (ret_pc_even 0x13940) by (first [lia | reflexivity]).
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m3) as MU.
  pose proof (wmono_refl rsegs m3) as WMO.
  do 8 zstep.
  (* the world is op_begin's result B1 (the machine's store order is the model's) *)
  assert (EB1 : upd (upd Bb 65544 (put 4 (-1))) 88 (put 4 (u_at Bb OFF_g_fail_next 1)) = B1)
    by (rewrite (op4_begin_world B Bb LBz eq_refl) in HB1; congruence).
  lazymatch goal with H : rw_cells rsegs ?mm W_BASE_PLAIN _ |- _ => rewrite EB1 in H end.
  assert (LB1a : Z.of_nat (length (upd Bb 65544 (put 4 (-1)))) = W_LEN)
    by (apply op4_len_put; [exact LBb | lia | cbn [Z.of_nat]; lia]).
  assert (FN1 : g_fail_next B1 = g_fail_next Bb).
  { rewrite <- EB1.
    rewrite op4_fn_put by (first [exact LB1a | cbn [Z.of_nat]; lia]).
    rewrite op4_fn_put by (first [exact LBb | cbn [Z.of_nat]; lia]).
    reflexivity. }
  (* the four zero doublewords are the struct's 32 zero bytes: the frame in op4_fr's shape *)
  lazymatch goal with HR : rw_cells rsegs ?m4 Sp _ |- _ =>
    assert (HRW4 : rw_cells rsegs m4 Sp
      ([C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s));
        CB 8 j10; C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff);
        C8 (Z_to_bv 64 (s32_at B 19792)); CB 32 (firstn 32 (skipn 8 j28))] ++
       [CB 32 (repeat (b8 0) 32)] ++
       [CB 8 (skipn 8 (skipn 8 (skipn 8 (skipn 40 (skipn 8 j28)))));
        C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
    by (apply (op4_rw_mid _ _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]);
        [ exact HR | cbn [cells_wf cell_wf]; rewrite repeat_length; tauto
        | cbn [cells_bytes cbytes]; rewrite o4e_zeros32, app_nil_r; reflexivity ]);
    cbn [app] in HRW4; rewrite o4e_sq in HRW4;
    assert (HM4 : op4_mem data D Sp lo B1 m0 m4
      (op4_fr (CB 8 j10) (Z_to_bv 64 (bv_swrap 32 (S_queued B))) (firstn 32 (skipn 8 j28)) (repeat (b8 0) 32)
              (skipn 8 (skipn 8 (skipn 8 (skipn 40 (skipn 8 j28)))))
              ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      by (eapply (op4_mem_after data D Sp lo 0 Bb B1 m0 m3); [exact HM3 | unfold LLVM_LOOP_K; lia | exact MU
          | exact WMO | exact HMI | exact HSTK
          | lazymatch goal with HW : rw_cells rsegs _ W_BASE_PLAIN [CB _ B1] |- _ => exact HW end
          | rewrite FN1; exact HFN | exact HRW4 | reflexivity])
  end.
  apply HK. unfold o4e_p60. do 21 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HN|]. split; [exact HC|]. split; [exact HC1|]. exact HM4.
Qed.

(* the model's three bytes on an empty cursor: kb = ab = db = 0 *)
Lemma o4e_m0 : forall c1, fi_n c1 = 0 ->
  o4_c3 D c1 = c1 /\ o4_display D c1 = 0 /\ o4_key D c1 = 65536.
Proof.
  intros c1 H0. unfold o4_c3, o4_display, o4_key.
  assert (Z0 : fuzz_u8_m D c1 = (c1, 0)) by (unfold fuzz_u8_m; rewrite H0; reflexivity).
  rewrite !Z0. cbn [fst snd]. rewrite !Z0. cbn [fst snd]. rewrite !Z0. cbn [fst snd].
  split; [reflexivity|]. split; reflexivity.
Qed.

(* fuzz_u8_m on a nonempty / an empty cursor (the ubsan twin,
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_lib.v fu8_nz / fu8_z) *)
Lemma o4e_u8 : forall c, fi_n c <> 0 ->
  fuzz_u8_m D c = (FuzzIn (fi_off c + 1) (fi_n c - 1), at8 D (Z.to_nat (fi_off c))).
Proof. intros c H. unfold fuzz_u8_m. destruct (Z.eqb_spec (fi_n c) 0); [lia | reflexivity]. Qed.

Lemma o4e_u8z : forall c, fi_n c = 0 -> fuzz_u8_m D c = (c, 0).
Proof. intros c H. unfold fuzz_u8_m. rewrite H. reflexivity. Qed.

(* the model's three bytes when the op byte leaves 1, 2, >= 3 bytes (fi_n c = 2, 3, >= 4) *)
Lemma o4e_mB : forall c, fi_n c = 2 ->
  o4_c3 D (fst (fuzz_u8_m D c)) = FuzzIn (fi_off c + 2) (fi_n c - 2) /\
  o4_display D (fst (fuzz_u8_m D c)) = 0 /\
  o4_key D (fst (fuzz_u8_m D c)) = KEY (at8 D (Z.to_nat (fi_off c + 1)) mod 9 + 1) 0.
Proof.
  intros c H. unfold o4_c3, o4_display, o4_key.
  rewrite (o4e_u8 c) by lia. cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1) (fi_n c - 1))) by (cbn [fi_n]; lia). cbn [fst snd fi_off fi_n].
  repeat (rewrite (o4e_u8z (FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1))) by (cbn [fi_n]; lia);
          cbn [fst snd fi_off fi_n]).
  replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia. replace (fi_n c - 1 - 1) with (fi_n c - 2) by lia.
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma o4e_mC : forall c, fi_n c = 3 ->
  o4_c3 D (fst (fuzz_u8_m D c)) = FuzzIn (fi_off c + 3) (fi_n c - 3) /\
  o4_display D (fst (fuzz_u8_m D c)) = 0 /\
  o4_key D (fst (fuzz_u8_m D c)) =
    KEY (at8 D (Z.to_nat (fi_off c + 1)) mod 9 + 1) (at8 D (Z.to_nat (fi_off c + 2))).
Proof.
  intros c H. unfold o4_c3, o4_display, o4_key.
  rewrite (o4e_u8 c) by lia. cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1) (fi_n c - 1))) by (cbn [fi_n]; lia). cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1))) by (cbn [fi_n]; lia). cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8z (FuzzIn (fi_off c + 1 + 1 + 1) (fi_n c - 1 - 1 - 1))) by (cbn [fi_n]; lia).
  cbn [fst snd fi_off fi_n].
  replace (fi_off c + 1 + 1 + 1) with (fi_off c + 3) by lia. replace (fi_n c - 1 - 1 - 1) with (fi_n c - 3) by lia.
  replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma o4e_mD : forall c, 4 <= fi_n c ->
  o4_c3 D (fst (fuzz_u8_m D c)) = FuzzIn (fi_off c + 4) (fi_n c - 4) /\
  o4_display D (fst (fuzz_u8_m D c)) = Z.land (at8 D (Z.to_nat (fi_off c + 3))) 1 /\
  o4_key D (fst (fuzz_u8_m D c)) =
    KEY (at8 D (Z.to_nat (fi_off c + 1)) mod 9 + 1) (at8 D (Z.to_nat (fi_off c + 2))).
Proof.
  intros c H. unfold o4_c3, o4_display, o4_key.
  rewrite (o4e_u8 c) by lia. cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1) (fi_n c - 1))) by (cbn [fi_n]; lia). cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1 + 1) (fi_n c - 1 - 1))) by (cbn [fi_n]; lia). cbn [fst snd fi_off fi_n].
  rewrite (o4e_u8 (FuzzIn (fi_off c + 1 + 1 + 1) (fi_n c - 1 - 1 - 1))) by (cbn [fi_n]; lia).
  cbn [fst snd fi_off fi_n].
  replace (fi_off c + 1 + 1 + 1 + 1) with (fi_off c + 4) by lia.
  replace (fi_n c - 1 - 1 - 1 - 1) with (fi_n c - 4) by lia.
  replace (fi_off c + 1 + 1 + 1) with (fi_off c + 3) by lia.
  replace (fi_off c + 1 + 1) with (fi_off c + 2) by lia.
  split; [reflexivity|]. split; reflexivity.
Qed.

(* one byte of the input buffer, as bytes_at reads it (LLVMFuzzerTestOneInput_disp.v disp_sub1) *)
Lemma o4e_sub1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (b8 0)].
Proof.
  induction l as [|d l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.
(* the cursor after the op byte *)
Lemma o4e_cur1 : forall c c1, fi_n c <> 0 -> llvm_cursor D c -> c1 = fst (fuzz_u8_m D c) ->
  c1 = FuzzIn (fi_off c + 1) (fi_n c - 1) /\ llvm_cursor D c1.
Proof.
  intros c c1 HN HC HC1. rewrite (o4e_u8 c HN) in HC1. cbn [fst] in HC1. subst c1.
  split; [reflexivity|]. unfold llvm_cursor in *. cbn [fi_off fi_n]. lia.
Qed.

(* the struct after the key store (0x13998 / 0x13b34 / 0x13bf4 `sw ..., 0x6c(sp)`, which splits the zeroed struct
   cell into 28 zero bytes and the key word) is the predicate's cmd_struct; the invariant is carried over the
   stretch from 0x13960 *)
Lemma o4e_fin_mem : forall Sp lo B1 m0 m m' j10 bf j30 j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 key,
  op4_mem data D Sp lo B1 m0 m
    (op4_fr (CB 8 j10) bf j30 (repeat (b8 0) 32) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  munch [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' lo Sp -> wmem rsegs m' B1 ->
  rw_cells rsegs m' Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30;
     CB 28 (firstn 28 (repeat (b8 0) 32)); C4 (Z_to_bv 64 key); CB 8 j70;
     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  op4_mem data D Sp lo B1 m0 m'
    (op4_fr (CB 8 j10) bf j30 (cmd_struct (repeat (b8 0) 24) 0 0 key) j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros Sp lo B1 m0 m m' j10 bf j30 j70 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 key HM MU WMO MI ST WM HR.
  pose proof HM as HMc. unfold op4_mem in HMc.
  destruct HMc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFN & _ & _).
  eapply (op4_mem_after data D Sp lo 0 B1 B1 m0 m m'); [exact HM | unfold LLVM_LOOP_K; lia | exact MU | exact WMO
    | exact MI | exact ST | exact WM | exact HFN | | reflexivity].
  unfold op4_fr.
  apply (op4_rw_mid m' Sp
    [C8 (Z_to_bv 64 (2 ^ 32 - 3)); C8 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)); CB 8 j10;
     C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 bf; CB 32 j30]
    [CB 28 (firstn 28 (repeat (b8 0) 32)); C4 (Z_to_bv 64 key)]
    [CB 32 (cmd_struct (repeat (b8 0) 24) 0 0 key)]
    [CB 8 j70; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  - exact HR.
  - cbn [cells_wf cell_wf]. split; [|exact I].
    unfold cmd_struct. rewrite !length_app, repeat_length, length_put. reflexivity.
  - cbn [cells_bytes cbytes]. rewrite le4_put, !app_nil_r. unfold cmd_struct. reflexivity.
Qed.

(* (A) 0x13960 beqz s6 taken (fi_n c1 = 0), 0x13b28-0x13b38: s7 = 0, a0 = 0, key = 0x10000, j 0x13df4 *)
Lemma o4e_A : forall Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    o4e_p60 m0 gp tp Sp lo ops c c1 B B1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    fi_n c1 = 0 ->
    (forall ms', op4_j data D m0 gp tp Sp lo ops (o4_c3 D c1) B1 (S_queued B) (o4_display D c1) (o4_key D c1)
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q H H0 HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 &
                 m & j10 & j30 & j70 & -> & HOPS & HN & HC & HC1 & HM).
  destruct (o4e_cur1 c c1 HN HC HC1) as [_ HCc1].
  destruct (o4e_m0 c1 H0) as (E3 & ED & EK). rewrite E3, ED, EK in HK.
  pose proof HM as HM0.
  unfold op4_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  unfold op4_fr in HRW.
  wk_facts.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  rewrite H0.
  zstep. if_cases K; [clear K | zify_cond K; lia].
  do 5 zstep.
  pose proof (u_at_range B A_S_queued 4) as HQR. change (8 * Z.of_nat 4) with 32 in HQR.
  apply HK. unfold op4_j. rewrite H0. do 22 eexists. split; [reflexivity|].
  split; [unfold o4_ok, S_queued; split; [exact HOPS|]; split; [exact HCc1|]; lia|].
  eapply (o4e_fin_mem Sp lo B1 m0 m); [exact HM0 | exact MU | exact WMO | exact HMI | exact HSTK
    | lazymatch goal with HW : rw_cells rsegs _ W_BASE_PLAIN [CB _ B1] |- _ => exact HW end | exact HRW].
Qed.

(* the compiler's b / 9 (LLVMFuzzerTestOneInput_disp.v dis_div): (b * 57) >> 9 on a byte *)
Lemma o4e_div9 : forall b, 0 <= b < 256 -> b * 57 / 512 = b / 9.
Proof.
  intros b Hb.
  assert (Hr : 0 <= b mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod b 9 ltac:(lia)) as E.
  assert (Hq : 0 <= b / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (b / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  replace (b * 57) with (512 * (b / 9) + (b / 9 + 57 * (b mod 9))) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (b / 9 + 57 * (b mod 9)) 512) by lia. lia.
Qed.

Lemma o4e_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* 0x13964-0x13984: a1 = ((kb - q - 8 q + 1) & 0xff) << 16 with q = (kb * 57) >> 9, as the kit leaves it: the
   key's kind kb % 9 + 1 (fuzz_transport.c:1073 `c.key = DIGINET_KEY(kb % 9 + 1, ab)`) shifted to bits 16.. *)
Lemma o4e_kw : forall kb, 0 <= kb < 256 ->
  Z.shiftl
    (Z.land
       ((bv_swrap 32
           (bv_swrap 32 (kb - Z.shiftr (kb * 57 mod 18446744073709551616) 9) mod 18446744073709551616 -
            Z.shiftl (Z.shiftr (kb * 57 mod 18446744073709551616) 9) 3 mod 18446744073709551616) + 1)
        mod 18446744073709551616) 255) 16
  = (kb mod 9 + 1) * 65536.
Proof.
  intros kb Hk.
  rewrite (Z.mod_small (kb * 57) 18446744073709551616) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 9) with 512.
  rewrite o4e_div9 by exact Hk.
  assert (Hq : 0 <= kb / 9 <= 28).
  { split; [apply Z.div_pos; lia|].
    assert (kb / 9 < 29) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hr : 0 <= kb mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod kb 9 ltac:(lia)) as E.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 16) with 65536.
  rewrite (o4e_swrap32 (kb - kb / 9)) by lia.
  rewrite (Z.mod_small (kb - kb / 9) 18446744073709551616) by lia.
  rewrite (Z.mod_small (kb / 9 * 8) 18446744073709551616) by lia.
  rewrite (o4e_swrap32 (kb - kb / 9 - kb / 9 * 8)) by lia.
  replace (kb - kb / 9 - kb / 9 * 8 + 1) with (kb mod 9 + 1) by lia.
  rewrite (Z.mod_small (kb mod 9 + 1) 18446744073709551616) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small (kb mod 9 + 1) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  reflexivity.
Qed.

(* DIGINET_KEY of a kind and an address byte, as numbers *)
Lemma o4e_lor_add : forall k ab, 0 <= k -> 0 <= ab < 65536 -> Z.lor (k * 65536) ab = k * 65536 + ab.
Proof.
  intros k ab Hk Hab.
  assert (HL : Z.land (k * 65536) ab = 0).
  { rewrite <- (Z.mod_small ab (2 ^ 16)) by (change (2 ^ 16) with 65536; lia).
    rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm ab), Z.land_assoc, Z.land_ones by lia.
    rewrite Z.mod_mul by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land (k * 65536) ab). lia.
Qed.

Lemma o4e_key_add : forall k ab, 0 <= k -> 0 <= ab < 65536 -> KEY k ab = k * 65536 + ab.
Proof.
  intros k ab Hk Hab. unfold KEY.
  change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small ab (2 ^ 16)) by (change (2 ^ 16) with 65536; lia).
  apply o4e_lor_add; lia.
Qed.

Lemma o4e_key0 : forall k, KEY k 0 = k * 65536.
Proof. intros k. unfold KEY. rewrite Z.land_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma o4e_land1 : forall x, 0 <= Z.land x 1 <= 1.
Proof.
  intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as E.
  change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E. rewrite E.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma o4e_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

(* (B, C, D) 0x13960 beqz s6 not taken (fi_n c1 <> 0): kb at 0x13964, the key's kind; then
   (B) fi_n c = 2, 0x13990-0x139a0: s7 = 0, a0 = 0, key = kind << 16, s3 = s4 + 2;
   (C) fi_n c = 3, 0x13bec-0x13c0c: ab, key = kind << 16 | ab, s7 = 0, a0 = 0, s3 = s4 + 3;
   (D) fi_n c >= 4, 0x13bec-0x13bfc and 0x13de4-0x13df0: ab, the key, db, s7 = s7 - 4, s3 = s4 + 4, a0 = db & 1 *)
Lemma o4e_K : forall Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms
    (Q : machine_state -> Prop),
    o4e_p60 m0 gp tp Sp lo ops c c1 B B1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    fi_n c1 <> 0 ->
    (forall ms', op4_j data D m0 gp tp Sp lo ops (o4_c3 D c1) B1 (S_queued B) (o4_display D c1) (o4_key D c1)
                   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.
Proof.
  intros Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q H H0 HK.
  destruct H as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 &
                 m & j10 & j30 & j70 & -> & HOPS & HN & HC & HC1 & HM).
  destruct (o4e_cur1 c c1 HN HC HC1) as [E1 HCc1].
  rewrite HC1 in HK.
  rewrite E1 in H0 |- *. cbn [fi_off fi_n] in H0 |- *.
  pose proof HM as HM0.
  unfold op4_mem in HM.
  destruct HM as (_ & _ & HD & HSP & HSTK & HLO & HSP2 & HWOS & HOWS & HOW & HOWIN & HMI & HRO & HWM & HFN & HRW & HSZ).
  unfold off_world in HOW. unfold off_window in HOWIN.
  assert (HLO0 : 0 <= lo) by (unfold W_BASE_PLAIN, W_LEN in HOWS; lia).
  unfold LLVM_FP, LLVM_LOOP_K, LLVM_FRAME in *.
  rewrite unsigned_lit in HOWIN by lia.
  unfold op4_fr in HRW.
  wk_facts.
  pose proof HC as HCc. unfold llvm_cursor, FUZZ_INPUT_MAX in HCc.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof (bytes_at_read rsegs m data D (fi_off c + 1) 1 HD ltac:(lia) ltac:(lia)) as HR1.
  rewrite o4e_sub1 in HR1 by lia.
  pose proof (u_at_range B A_S_queued 4) as HQR. change (8 * Z.of_nat 4) with 32 in HQR.
  pose proof (munch_refl [(Sp - 0, Sp + 224); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* 0x13960 beqz s6: not taken *)
  zstep. if_cases K; [zify_cond K; lia | clear K].
  (* 0x13964-0x1398c: kb, the kind << 16, bne s7, 2 *)
  do 11 zstep.
  pose proof (o4e_byte (nth (Z.to_nat (fi_off c + 1)) D (b8 0))) as HKB.
  set (kb := bv_unsigned (nth (Z.to_nat (fi_off c + 1)) D (b8 0))) in *.
  rewrite (o4e_kw kb HKB).
  pose proof (Z.mod_pos_bound kb 9 ltac:(lia)) as HK9.
  if_cases K; zify_cond K.
  - (* fi_n c <> 2: 0x13bec lbu ab, or, sw the key, bne s7, 3 *)
    pose proof (bytes_at_read rsegs m data D (fi_off c + 2) 1 HD ltac:(lia) ltac:(lia)) as HR2.
    rewrite o4e_sub1 in HR2 by lia.
    do 2 zstep.
    pose proof (o4e_byte (nth (Z.to_nat (fi_off c + 2)) D (b8 0))) as HAB.
    set (ab := bv_unsigned (nth (Z.to_nat (fi_off c + 2)) D (b8 0))) in *.
    rewrite (o4e_lor_add (kb mod 9 + 1) ab) by lia.
    do 3 zstep.
    if_cases K3; zify_cond K3.
    + (* (D) fi_n c <> 3: 0x13de4-0x13df0 db, s7 - 4, s3 = s4 + 4, a0 = db & 1 *)
      assert (HN4 : 4 <= fi_n c) by lia.
      lazymatch goal with HDx : bytes_at rsegs ?mm data D |- _ =>
        pose proof (bytes_at_read rsegs mm data D (fi_off c + 3) 1 HDx ltac:(lia) ltac:(lia)) as HR3 end.
      rewrite o4e_sub1 in HR3 by lia.
      do 4 zstep.
      pose proof (o4e_byte (nth (Z.to_nat (fi_off c + 3)) D (b8 0))) as HDBY.
      set (db := bv_unsigned (nth (Z.to_nat (fi_off c + 3)) D (b8 0))) in *.
      destruct (o4e_mD c HN4) as (E3 & ED & EK). rewrite E3, ED, EK in HK.
      unfold at8, bz in HK.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 1)) D (b8 0))) with kb in HK.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 2)) D (b8 0))) with ab in HK.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 3)) D (b8 0))) with db in HK.
      rewrite o4e_key_add in HK by lia.
      apply HK. unfold op4_j. cbn [fi_off fi_n].
      replace (data + (fi_off c + 4)) with (data + fi_off c + 4) by lia.
      replace (fi_n c - 4) with (fi_n c + -4) by lia.
      do 22 eexists. split; [reflexivity|].
      split; [unfold o4_ok, S_queued, llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n];
              pose proof (o4e_land1 db); split; [exact HOPS|]; lia|].
      eapply (o4e_fin_mem Sp lo B1 m0 m); [exact HM0 | exact MU | exact WMO | exact HMI | exact HSTK
        | lazymatch goal with HW : rw_cells rsegs _ W_BASE_PLAIN [CB _ B1] |- _ => exact HW end | exact HRW].
    + (* (C) fi_n c = 3: 0x13c00-0x13c0c s7 = 0, a0 = 0, s3 = s4 + 3 *)
      assert (E3' : fi_n c = 3) by lia.
      do 4 zstep.
      destruct (o4e_mC c E3') as (E3 & ED & EK). rewrite E3, ED, EK in HK.
      unfold at8, bz in HK.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 1)) D (b8 0))) with kb in HK.
      change (bv_unsigned (nth (Z.to_nat (fi_off c + 2)) D (b8 0))) with ab in HK.
      rewrite o4e_key_add in HK by lia.
      apply HK. unfold op4_j. cbn [fi_off fi_n].
      replace (data + (fi_off c + 3)) with (data + fi_off c + 3) by lia.
      replace (fi_n c - 3) with 0 by lia.
      do 22 eexists. split; [reflexivity|].
      split; [unfold o4_ok, S_queued, llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n];
              split; [exact HOPS|]; lia|].
      eapply (o4e_fin_mem Sp lo B1 m0 m); [exact HM0 | exact MU | exact WMO | exact HMI | exact HSTK
        | lazymatch goal with HW : rw_cells rsegs _ W_BASE_PLAIN [CB _ B1] |- _ => exact HW end | exact HRW].
  - (* (B) fi_n c = 2: 0x13990-0x139a0 *)
    assert (E2 : fi_n c = 2) by lia.
    destruct (o4e_mB c E2) as (E3 & ED & EK). rewrite E3, ED, EK in HK.
    unfold at8, bz in HK. change (bv_unsigned (nth (Z.to_nat (fi_off c + 1)) D (b8 0))) with kb in HK.
    rewrite o4e_key0 in HK.
    do 5 zstep.
    apply HK. unfold op4_j. cbn [fi_off fi_n].
    replace (data + (fi_off c + 2)) with (data + fi_off c + 2) by lia.
    replace (fi_n c - 2) with 0 by lia.
    do 22 eexists. split; [reflexivity|].
    split; [unfold o4_ok, S_queued, llvm_cursor, FUZZ_INPUT_MAX; cbn [fi_off fi_n];
            split; [exact HOPS|]; lia|].
    eapply (o4e_fin_mem Sp lo B1 m0 m); [exact HM0 | exact MU | exact WMO | exact HMI | exact HSTK
      | lazymatch goal with HW : rw_cells rsegs _ W_BASE_PLAIN [CB _ B1] |- _ => exact HW end | exact HRW].
Qed.

(* 0x13910 -> 0x13df4: the common stretch, then the four key-byte subcases *)
Lemma o4e_entry : op4_entry_stmt data D.
Proof.
  unfold op4_entry_stmt.
  intros Sp lo ops c c1 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q MSC H HB1 HK.
  eapply o4e_pre; [exact MSC | exact H | exact HB1 |].
  intros ms' H60.
  destruct (Z.eq_dec (fi_n c1) 0) as [Z0|NZ].
  - eapply o4e_A; [exact H60 | exact Z0 | exact HK].
  - eapply o4e_K; [exact H60 | exact NZ | exact HK].
Qed.

End OP4E.

Lemma op4_entry : forall data D, op4_entry_stmt data D.
Proof. exact o4e_entry. Qed.
