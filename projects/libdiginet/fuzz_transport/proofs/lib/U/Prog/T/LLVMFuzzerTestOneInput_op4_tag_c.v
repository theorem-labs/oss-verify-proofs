(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x142e8 .. 0x14384 (fuzz/fuzz_transport.c:1097-1101):
   at = -1 unless coalescable(key) (inlined: key & 0xf70000 = 0 or key & 0xff0000 = 0x90000 is not, t4_coal0) and
   g_nq <> 0; then the loop 0x14330-0x14380 over g_q / g_cmd (TOps.v submit_find_at), proved by induction on the
   model's fuel. Its two UBSan traps (i reaching 1024 at 0x14334, g_q[i] past g_cmd at 0x14340) are the model's None;
   s4 holds at as an unsigned 32-bit value (0xffffffff for -1). *)
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

Lemma t4_sub28 : forall (pre x R : list byte), length pre = 28%nat -> length x = 4%nat -> sub (pre ++ x ++ R) 28 4 = x.
Proof.
  intros pre x R Lp Lx. unfold sub. change (Z.to_nat 28) with 28%nat.
  rewrite skipn_app, Lp, (skipn_all2 pre) by lia. rewrite app_nil_l.
  replace (28 - 28)%nat with 0%nat by lia. change (skipn 0 (x ++ R)) with (x ++ R).
  rewrite firstn_app, Lx. replace (4 - 4)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  apply firstn_all2. lia.
Qed.

(* the key at sp+0x7c (the struct's offset 28) *)
Lemma t4_J28 : forall B1 D c3 display key jhi, llvm_cursor D c3 ->
  sub (t4_cs B1 D c3 display key ++ jhi) 28 4 = le4 (Z_to_bv 64 key).
Proof.
  intros B1 D c3 display key jhi HC. pose proof (t4_cbD D c3 HC) as (H1 & H2 & H3).
  pose proof (t4_cb_len B1 D c3 H1 H2 H3) as L.
  rewrite le4_put.
  replace (t4_cs B1 D c3 display key ++ jhi)
    with ((t4_cb B1 D c3 ++ [b8 (t4_len D c3); b8 display; b8 0; b8 0]) ++ put 4 key ++ jhi)
    by (unfold t4_cs, cmd_struct; rewrite <- !app_assoc; reflexivity).
  apply t4_sub28; [rewrite app_length, L; reflexivity | apply length_put].
Qed.

Lemma t4_zx32 : forall v, 0 <= v < 2 ^ 32 -> zx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* one turn of submit_find_at below g_nq *)
Lemma t4_find_inv : forall f B key i at_, submit_find_at (S f) B key i = Some at_ -> i < g_nq B ->
  i < CMDS_MAX /\ Q_at B i < CMDS_MAX /\
  ((Cmd_key B (Q_at B i) = key /\ at_ = i) \/
   (Cmd_key B (Q_at B i) <> key /\ submit_find_at f B key (i + 1) = Some at_)).
Proof.
  intros f B key i at_ H Hi. rewrite t4_findat_step in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H.
  destruct (CMDS_MAX <=? i) eqn:C1; [discriminate H|]. apply Z.leb_gt in C1.
  destruct (CMDS_MAX <=? Q_at B i) eqn:C2; [discriminate H|]. apply Z.leb_gt in C2.
  split; [exact C1|]. split; [exact C2|].
  destruct (Cmd_key B (Q_at B i) =? key) eqn:C3.
  - left. apply Z.eqb_eq in C3. split; [exact C3|]. injection H as <-. reflexivity.
  - right. apply Z.eqb_neq in C3. split; [exact C3 | exact H].
Qed.

Lemma t4_find_out : forall f B key i at_, submit_find_at f B key i = Some at_ -> g_nq B <= i -> at_ = -1.
Proof.
  intros [|f] B key i at_ H Hi; [discriminate H|].
  rewrite t4_findat_step, (proj2 (Z.ltb_ge _ _) Hi) in H. injection H as <-. reflexivity.
Qed.

(* the sign extension of a 32-bit value (sext.w): small values stay, a closed one is computed *)
Ltac t4_sw :=
  repeat match goal with
  | |- context [bv_swrap 32 ?x] =>
      first [ rewrite (swrap32_small x) by lia
            | (let v0 := wk_zval x in let v := eval vm_compute in (bv_swrap 32 v0) in
               change (bv_swrap 32 x) with v) ]
  end.

Lemma t4_D : forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ (Q : machine_state -> Prop),
  t4_SC data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
  t4_atopt B1 key = Some at_ ->
  (forall ms', t4_SD data D regs0 m0 Sp lo ops before c3 B1 display key F fc at_ ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms at_ Q H HAT HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jio & jhi & -> &
                 E0 & E2 & E3 & E5 & E6 & E8 & E9 & E10 & E11 & HOK & LJHI & HM).
  subst s0 s2 s3 s5 s6 s8 s9 s10 s11.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof (t4_mem_facts _ _ _ _ _ _ _ _ _ _ _ HM) as
    (HD0 & HDL & HLO & HSP2 & HWL & HSP16 & HJ1 & HJ2 & HJ3 & HMI & _ & _ & _ & HWM & _ & LB & _).
  pose proof (t4_nq_rng (t4_B2 B1)) as HNQ.
  pose proof (t4_mem_rd60 _ _ _ _ _ _ _ _ _ _ _ 28 4%nat (Sp + 124) HM ltac:(lia) ltac:(lia) ltac:(lia)) as HRk.
  rewrite (t4_J28 B1 D c3 display key jhi HCUR) in HRk.
  (* ---- the exit 0x14384, s4 = at ---- *)
  assert (EXIT : forall x0 x1 x2 x3 x4 x5 x6 x7 xs4 : word, xs4 = Z_to_bv 64 (at_ mod 2 ^ 32) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                         (Z_to_bv 64 (g_ncmd B1)) s1 x0 x1 x2 x3 x4 x5 x6 x7
                         (Z_to_bv 64 (229576 + g_ncmd B1 * 40)) (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                         xs4 (Z_to_bv 64 229576) (Z_to_bv 64 (t4_n D c3)) s7
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                         (Z_to_bv 64 (Z.b2z (t4_sys B1 D c3))) (Z_to_bv 64 ops) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14384) fc None m (seg_rom rsegs))).
  { intros x0 x1 x2 x3 x4 x5 x6 x7 xs4 Exs4. apply HK. unfold t4_SD.
    do 28 eexists. exists m, jio, jhi.
    split; [reflexivity|].
    do 3 (split; [t4_weq|]). split; [exact Exs4|]. do 6 (split; [t4_weq|]).
    split; [exact HOK|]. split; [exact LJHI|]. exact HM. }
  (* ---- the search loop 0x14330 at index i ---- *)
  assert (LOOP : forall (f : nat) (i : Z) (x0 x1 x2 x3 x4 x5 x6 x7 xs4 : word),
    submit_find_at f (t4_B2 B1) key i = Some at_ -> 0 <= i < g_nq (t4_B2 B1) ->
    x0 = Z_to_bv 64 key -> x1 = Z_to_bv 64 (g_nq (t4_B2 B1)) -> x2 = Z_to_bv 64 i -> x3 = Z_to_bv 64 (i + 1) ->
    x4 = Z_to_bv 64 (270536 + 4 * i) -> x5 = Z_to_bv 64 4294967295 ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2
                         (Z_to_bv 64 (g_ncmd B1)) s1 x0 x1 x2 x3 x4 x5 x6 x7
                         (Z_to_bv 64 (229576 + g_ncmd B1 * 40)) (Z_to_bv 64 (data + fi_off (t4_c5 D c3)))
                         xs4 (Z_to_bv 64 229576) (Z_to_bv 64 (t4_n D c3)) s7
                         (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                         (Z_to_bv 64 (Z.b2z (t4_sys B1 D c3))) (Z_to_bv 64 ops) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14330) fc None m (seg_rom rsegs))).
  { induction f as [|f IH]; intros i x0 x1 x2 x3 x4 x5 x6 x7 xs4 HF Hi E0 E1 E2 E3 E4 E5;
      [discriminate HF|].
    subst x0 x1 x2 x3 x4 x5.
    destruct (t4_find_inv f (t4_B2 B1) key i at_ HF (proj2 Hi)) as (HI1 & HQ1 & HCASE).
    unfold CMDS_MAX in HI1, HQ1.
    pose proof (t4_qat_rng (t4_B2 B1) i) as HQR.
    pose proof (t4_key_rng (t4_B2 B1) (Q_at (t4_B2 B1) i)) as HKR.
    (* 0x14330 li a6, 0x401; 0x14334 beq a3, a6 (i = 1024: trap) *)
    zstep. zstep. t4_br.
    (* 0x14338 lw a6, 0(a4): g_q[i] *)
    zstep.
    rewrite (t4_s32_small (t4_B2 B1) (60872 + 4 * i))
      by (change (u_at (t4_B2 B1) (60872 + 4 * i) 4) with (Q_at (t4_B2 B1) i); lia).
    change (u_at (t4_B2 B1) (60872 + 4 * i) 4) with (Q_at (t4_B2 B1) i).
    (* 0x1433c li a7, 0x3ff; 0x14340 bltu a7, a6 (g_q[i] > 1023: trap) *)
    zstep. zstep. t4_br.
    (* 0x14344 li a7, 0x28; 0x14348 mul a6, a6, a7; 0x1434c not a7, s5; 0x14350 bltu a7, a6 (trap) *)
    do 4 zstep. t4_br.
    (* 0x14354 add a6, s5, a6; 0x14358 lwu a6, 4(a6): g_cmd[g_q[i]].key *)
    zstep. zstep.
    lazymatch goal with
    | |- context [u_at (t4_B2 B1) ?k 4] =>
        replace (u_at (t4_B2 B1) k 4) with (Cmd_key (t4_B2 B1) (Q_at (t4_B2 B1) i))
          by (unfold Cmd_key; f_equal; unfold A_Cmd_key, OFF_g_cmd in *; lia)
    end.
    (* 0x1435c mv s4, a2; 0x14360 beq a6, a0 *)
    zstep. zstep.
    destruct HCASE as [[EK EA] | [EK EF]].
    - (* the key matches: at = i *)
      t4_br.
      (* 0x14368 bgeu a3, a1 *)
      zstep.
      destruct (Z.lt_ge_cases (i + 1) (g_nq (t4_B2 B1))) as [LT|GE].
      + t4_br.
        (* 0x1436c addi a3, a3, 1; 0x14370 addi a2, a2, 1; 0x14374 sext.w a6, s4; 0x14378 addi a4, a4, 4;
           0x1437c mv a5, s4; 0x14380 bltz a6 (not taken: s4 = i >= 0) *)
        do 6 zstep. t4_sw. t4_br.
        apply EXIT. rewrite EA. t4_weq.
      + t4_br. apply EXIT. rewrite EA. t4_weq.
    - (* no match: 0x14364 mv s4, a5 *)
      t4_br. zstep.
      (* 0x14368 bgeu a3, a1 *)
      zstep.
      destruct (Z.lt_ge_cases (i + 1) (g_nq (t4_B2 B1))) as [LT|GE].
      + t4_br.
        do 6 zstep. t4_sw. t4_br.
        apply (IH (i + 1)); [exact EF | lia | t4_weq | t4_weq | t4_weq | t4_weq | t4_weq | t4_weq].
      + t4_br. apply EXIT. rewrite (t4_find_out f (t4_B2 B1) key (i + 1) at_ EF GE). t4_weq. }
  (* ---- 0x142e8 lwu a0, 0x7c(sp) (key); 0x142ec lui a1, 0xf70; 0x142f0 and a1, a0, a1; 0x142f4 li a2, -1;
     0x142f8 srli s4, a2, 32; 0x142fc beqz a1 ---- *)
  zstep.
  rewrite (t4_zx32 key HKEY).
  do 5 zstep.
  pose proof (land_lt_pow2 key 16187392 32 HKEY ltac:(lia)) as LK1.
  pose proof (land_lt_pow2 key 16711680 32 HKEY ltac:(lia)) as LK2.
  assert (HC0 : h_coalescable_m key = 0 -> at_ = -1).
  { intros EC. unfold t4_atopt in HAT. rewrite EC in HAT. change (negb (0 =? 0)) with false in HAT.
    cbv iota in HAT. injection HAT as <-. reflexivity. }
  destruct (Z.eq_dec (Z.land key 16187392) 0) as [K1|K1].
  { t4_br. apply EXIT. rewrite (HC0 (proj2 (t4_coal0 key HKEY) (or_introl K1))). t4_weq. }
  t4_br.
  (* ---- 0x14300 lui a1, 0xff0; 0x14304 and a1, a0, a1; 0x14308 lui a2, 0x90; 0x1430c beq a1, a2 ---- *)
  do 4 zstep.
  destruct (Z.eq_dec (Z.land key 16711680) 589824) as [K2|K2].
  { t4_br. apply EXIT. rewrite (HC0 (proj2 (t4_coal0 key HKEY) (or_intror K2))). t4_weq. }
  t4_br.
  assert (HF0 : submit_find_at (S (Z.to_nat CMDS_MAX)) (t4_B2 B1) key 0 = Some at_).
  { unfold t4_atopt in HAT.
    assert (NC : h_coalescable_m key <> 0) by (intros EC; apply (proj1 (t4_coal0 key HKEY)) in EC; tauto).
    rewrite (proj2 (Z.eqb_neq _ _) NC) in HAT. change (negb false) with true in HAT. cbv iota in HAT. exact HAT. }
  (* ---- 0x14310 lwu a1, 0xc(s9) (g_nq); 0x14314 beqz a1 ---- *)
  zstep.
  change (u_at (t4_B2 B1) 64980 4) with (g_nq (t4_B2 B1)).
  zstep.
  destruct (Z.eq_dec (g_nq (t4_B2 B1)) 0) as [NQ0|NQ0].
  { t4_br. apply EXIT. rewrite (t4_find_out _ (t4_B2 B1) key 0 at_ HF0 ltac:(lia)). t4_weq. }
  t4_br.
  (* ---- 0x14318 mv a2, zero; 0x1431c li a3, 1; 0x14320 auipc a4; 0x14324 addi a4 (&g_q); 0x14328 li a5, -1;
     0x1432c srli a5, a5, 32 ---- *)
  do 6 zstep.
  apply (LOOP _ 0 _ _ _ _ _ _ _ _ _ HF0); [lia | t4_weq | t4_weq | t4_weq | t4_weq | t4_weq | t4_weq].
Qed.
