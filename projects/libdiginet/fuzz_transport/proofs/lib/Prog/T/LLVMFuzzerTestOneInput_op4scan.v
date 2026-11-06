(* The two loops of the tagged arm of case 4 of the plain op loop of LLVMFuzzerTestOneInput (op_submit's g_raw == 0
   arm, fuzz/fuzz_transport.c:1093-1098; model TModel/TOps.v op_submit_m), as stand-alone loop lemmas over a bare
   machine state. Every register a loop does not touch is a variable it keeps; the memory is any m with the one read
   fact the loop needs, and it is unchanged at the exit. Addresses are from tr6/llvmf-plain.dis.

   - op4_sys_scan: the F0 13 xx 70 scan of :1093 (`sys = spec_system_at(c.bytes, c.len) >= 0`), loop 0x13fd0-0x13ff4
     and its two exits 0x13ff8 / 0x13ffc to 0x1400c: s5 = 1 exactly when DgnSpec's system_at of the first len
     bytes. The loop is proved by induction on the start positions left, with the invariant that no position below
     the counter is a hit (op4_sys_loop).
   - op4_find_scan: the queue search of :1094-1098 (`for (i = 0; i < g_nq; i++) if (g_cmd[g_q[i]].key == key)`),
     loop 0x14054-0x14088, exit 0x1408c: s2 = at_ (as the 32-bit value, 0xffffffff for -1) where TOps.v's
     submit_find_at says Some at_. Proved by induction on the model's fuel.

   The shapes follow an earlier version of the ubsan twin: its t4_sysloop of
   libdiginet/fuzz_transport lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_b.v (file sha256 c85b7abc5486; donor not released),
   and its t4_atloop of
   libdiginet/fuzz_transport lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_c.v (file sha256 8020364d26fc; donor not released);
   the model lemmas op4_sys_val, op4_sys_step and op4_find_step are the ubsan twin's t4_sys_val (generalised from 24
   bytes to any length), t4_sys_step and t4_findat_step (lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_lib.v,
   lib/U/Prog/T/LLVMFuzzerTestOneInput_op4_tag_m.v), which are build-independent. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  check_refusal_submit.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the model: system_at as the machine scans it *)

(* nth below n of a prefix of length n (ubsan _op4_tag_lib.v t4_nth_firstn) *)
Lemma op4_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros n i d Hi.
  - rewrite firstn_nil. destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; cbn [nth]; [reflexivity|].
    apply IH. lia.
Qed.

(* :1093 spec_system_at over the first len bytes: positions 0 .. len - 4, read in any list that starts with them *)
Lemma op4_sys_val : forall (cs : list byte) (len : Z), 3 <= len <= Z.of_nat (length cs) ->
  existsb (sys_hit cs) (seq 0 (Z.to_nat (len - 3))) = system_at (firstn (Z.to_nat len) cs).
Proof.
  intros cs len Hl.
  assert (LF : length (firstn (Z.to_nat len) cs) = Z.to_nat len) by (rewrite length_firstn; lia).
  unfold system_at. rewrite LF.
  replace (Z.to_nat (len - 3)) with (Z.to_nat len - 3)%nat by lia.
  assert (HE : forall i, (i + 3 < Z.to_nat len)%nat ->
            sys_hit cs i = sys_hit (firstn (Z.to_nat len) cs) i).
  { intros i Hi. unfold sys_hit, at8. rewrite !op4_nth_firstn by lia. reflexivity. }
  apply eq_true_iff_eq. rewrite !existsb_exists.
  split; intros [i [Hi Hh]]; exists i; apply in_seq in Hi; (split; [apply in_seq; lia|]).
  - rewrite <- (HE i ltac:(lia)). exact Hh.
  - rewrite (HE i ltac:(lia)). exact Hh.
Qed.

Lemma op4_sys_step : forall (b : list byte) (i : nat),
  existsb (sys_hit b) (seq 0 (S i)) = (existsb (sys_hit b) (seq 0 i) || sys_hit b i)%bool.
Proof.
  intros b i. rewrite seq_S, existsb_app. cbn [existsb orb].
  rewrite ?Nat.add_0_l, orb_false_r. reflexivity.
Qed.

(* 0x13fc0 `bltu a1, 4` -> 0x14008 `mv s5, zero`: under 4 bytes there is no position to test *)
Lemma op4_sys_short : forall (cs : list byte) (len : Z), len < 4 -> system_at (firstn (Z.to_nat len) cs) = false.
Proof.
  intros cs len Hl. unfold system_at.
  replace (length (firstn (Z.to_nat len) cs) - 3)%nat with 0%nat by (rewrite length_firstn; lia).
  reflexivity.
Qed.

(* the struct's first len bytes are its command bytes' (len <= 24 = length cb) *)
Lemma op4_sys_cmd : forall (cb : list byte) (len display key : Z), (Z.to_nat len <= length cb)%nat ->
  firstn (Z.to_nat len) (cmd_struct cb len display key) = firstn (Z.to_nat len) cb.
Proof.
  intros cb len display key H. unfold cmd_struct.
  rewrite firstn_app. replace (Z.to_nat len - length cb)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* ---------------------------------------------------------------- the model: submit_find_at *)

Lemma op4_find_step : forall f B key i,
  submit_find_at (S f) B key i =
    (if i <? g_nq B then
       if CMDS_MAX <=? i then None
       else if CMDS_MAX <=? Q_at B i then None
       else if Cmd_key B (Q_at B i) =? key then Some i
       else submit_find_at f B key (i + 1)
     else Some (-1)).
Proof. intros. reflexivity. Qed.

(* the answer is -1 or a queue position from i on *)
Lemma op4_find_rng : forall f B key i j, 0 <= i -> submit_find_at f B key i = Some j ->
  j = -1 \/ (i <= j < g_nq B /\ j < CMDS_MAX).
Proof.
  induction f as [|f IH]; intros B key i j Hi H; cbn [submit_find_at] in H; [discriminate H|].
  destruct (Z.ltb_spec i (g_nq B)) as [Hn|Hn]; [|injection H as <-; left; reflexivity].
  destruct (Z.leb_spec CMDS_MAX i) as [E|E]; [discriminate H|].
  destruct (CMDS_MAX <=? Q_at B i); [discriminate H|].
  destruct (Cmd_key B (Q_at B i) =? key).
  - injection H as <-. right. lia.
  - destruct (IH B key (i + 1) j ltac:(lia) H) as [HR|HR]; [left; exact HR | right; lia].
Qed.

(* bne / beq of two values below 2^64 *)
Lemma op4_eqb_uu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* 0x13ffc slti a0, a0, 0 of the scan's answer: 1 for -1 (0x13ff8), 0 for a position *)
Lemma op4_slti_m1 : v_slti (Z_to_bv 64 (-1)) 0 = Z_to_bv 64 1.
Proof. rewrite v_slti_b2z, unsigned_lit_wrap. reflexivity. Qed.

Lemma op4_slti_nonneg : forall v, 0 <= v < 2 ^ 63 -> v_slti (Z_to_bv 64 v) 0 = Z_to_bv 64 0.
Proof.
  intros v Hv. rewrite v_slti_b2z, unsigned_lit by lia.
  rewrite zb_lxor_pow2_small by lia.
  replace (v + 2 ^ 63 <? 0 + 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* ---------------------------------------------------------------- 0x13fd0: the F0 13 xx 70 scan *)

(* The loop from position i: a0 = i, a1 = len - 3 (0x13fc8), a2 = p + 1 + i (0x13fcc addi a2, sp, 0x51 with
   p = sp + 0x50), s2 = 0xf0 (0x13f64), s7 = 0x13 (0x13f68); 0x13fe4 compares the fourth byte with 0x70. *)
Lemma op4_sys_loop : forall (cs : list byte) (p len : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m p cs -> 4 <= len <= Z.of_nat (length cs) -> len < 2 ^ 63 ->
  (forall a0' a2' a3' a4' : word,
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (len - 3)) a2' a3' a4' a5 a6 a7
                (Z_to_bv 64 0xf0) s3 s4 (Z_to_bv 64 (b2z (existsb (sys_hit cs) (seq 0 (Z.to_nat (len - 3))))))
                s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1400c) fc None m (seg_rom rsegs))) ->
  forall (r : nat) (i : Z) (a3 a4 s5 : word),
    0 <= i -> Z.of_nat r = len - 3 - i -> (0 < r)%nat ->
    existsb (sys_hit cs) (seq 0 (Z.to_nat i)) = false ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (p + 1 + i))
               a3 a4 a5 a6 a7 (Z_to_bv 64 0xf0) s3 s4 s5 s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fd0) fc None m (seg_rom rsegs)).
Proof.
  intros cs p len Q ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HB HL HL63 K.
  pose proof (bytes_at_bound rsegs m p cs HB) as HPB.
  induction r as [|r IH]; intros i a3 a4 s5 Hi Hr Hrp HINV; [lia|].
  pose proof (rd1 m p cs i HB ltac:(lia) ltac:(lia)) as RD0.
  pose proof (rd1 m p cs (i + 1) HB ltac:(lia) ltac:(lia)) as RD1.
  pose proof (rd1 m p cs (i + 3) HB ltac:(lia) ltac:(lia)) as RD3.
  pose proof (u_at_range cs i 1) as R0. cbn [Z.of_nat] in R0.
  pose proof (u_at_range cs (i + 1) 1) as R1. cbn [Z.of_nat] in R1.
  pose proof (u_at_range cs (i + 3) 1) as R3. cbn [Z.of_nat] in R3.
  assert (EU0 : u_at cs i 1 = at8 cs (Z.to_nat i)) by (apply u_at_1; lia).
  assert (EU1 : u_at cs (i + 1) 1 = at8 cs (S (Z.to_nat i)))
    by (replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia; apply u_at_1; lia).
  assert (EU3 : u_at cs (i + 3) 1 = at8 cs (S (S (S (Z.to_nat i)))))
    by (replace (S (S (S (Z.to_nat i)))) with (Z.to_nat (i + 3)) by lia; apply u_at_1; lia).
  (* the miss: 0x13fec addi a0, a0, 1;  0x13ff0 addi a2, a2, 1;  0x13ff4 bne a1, a0 -> 0x13fd0 *)
  assert (NEXT : forall a3' a4' : word, sys_hit cs (Z.to_nat i) = false ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (p + 1 + i))
               a3' a4' a5 a6 a7 (Z_to_bv 64 0xf0) s3 s4 s5 s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fec) fc None m (seg_rom rsegs))).
  { intros a3' a4' MISS.
    assert (HINV1 : existsb (sys_hit cs) (seq 0 (Z.to_nat (i + 1))) = false).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite op4_sys_step, HINV, MISS. reflexivity. }
    do 3 step.
    rewrite (op4_eqb_uu (len - 3) (i + 1)) by lia.
    destruct (Z.eqb_spec (len - 3) (i + 1)) as [E|E]; cbn [negb].
    - (* no position left: 0x13ff8 addi a0, zero, -1;  0x13ffc slti;  0x14000 xori;  0x14004 j 0x1400c *)
      do 4 step.
      assert (EF : existsb (sys_hit cs) (seq 0 (Z.to_nat (len - 3))) = false) by (rewrite E; exact HINV1).
      rewrite EF in K.
      rewrite op4_slti_m1, unsigned_lit by lia. change (Z.lxor 1 1) with (b2z false).
      apply K.
    - (* another position: back to 0x13fd0 *)
      replace (p + 1 + i + 1) with (p + 1 + (i + 1)) by lia.
      apply (IH (i + 1)); [lia | lia | lia | exact HINV1]. }
  (* ---- 0x13fd0 lbu a3, -1(a2);  0x13fd4 bne a3, s2 -> 0x13fec ---- *)
  step.
  rewrite (wm_lbu cs i).
  step.
  rewrite (eqb_ss (u_at cs i 1) 240) by lia.
  destruct (Z.eqb_spec (u_at cs i 1) 240) as [B0|B0]; cbn [negb].
  2: { apply NEXT. unfold sys_hit. rewrite <- EU0.
       replace (u_at cs i 1 =? 0xf0) with false by (symmetry; apply Z.eqb_neq; exact B0). reflexivity. }
  (* ---- 0x13fd8 lbu a3, 0(a2);  0x13fdc bne a3, s7 -> 0x13fec ---- *)
  step.
  rewrite (wm_lbu cs (i + 1)).
  step.
  rewrite (eqb_ss (u_at cs (i + 1) 1) 19) by lia.
  destruct (Z.eqb_spec (u_at cs (i + 1) 1) 19) as [B1|B1]; cbn [negb].
  2: { apply NEXT. unfold sys_hit. rewrite <- EU1.
       replace (u_at cs (i + 1) 1 =? 0x13) with false by (symmetry; apply Z.eqb_neq; exact B1).
       rewrite !andb_false_r. reflexivity. }
  (* ---- 0x13fe0 lbu a3, 2(a2);  0x13fe4 addi a4, zero, 0x70;  0x13fe8 beq a3, a4 -> 0x13ffc ---- *)
  step.
  rewrite (wm_lbu cs (i + 3)).
  do 2 step.
  rewrite (eqb_ss (u_at cs (i + 3) 1) 112) by lia.
  destruct (Z.eqb_spec (u_at cs (i + 3) 1) 112) as [B3|B3]; cbv iota.
  2: { apply NEXT. unfold sys_hit. rewrite <- EU3.
       replace (u_at cs (i + 3) 1 =? 0x70) with false by (symmetry; apply Z.eqb_neq; exact B3).
       rewrite !andb_false_r. reflexivity. }
  (* a hit at i: 0x13ffc slti a0, a0, 0;  0x14000 xori s5, a0, 1;  0x14004 j 0x1400c *)
  assert (HHIT : existsb (sys_hit cs) (seq 0 (Z.to_nat (len - 3))) = true).
  { apply existsb_exists. exists (Z.to_nat i). split; [apply in_seq; lia|].
    unfold sys_hit. rewrite <- EU0, <- EU1, <- EU3, B0, B1, B3. reflexivity. }
  do 3 step.
  rewrite HHIT in K.
  rewrite (op4_slti_nonneg i), unsigned_lit by lia. change (Z.lxor 0 1) with (b2z true).
  apply K.
Qed.

(* The scan from its head 0x13fd0 (i = 0) to 0x1400c: s5 = b2z (system_at of the first len bytes at p). *)
Lemma op4_sys_scan : forall (cs : list byte) (p len : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m p cs -> 4 <= len <= Z.of_nat (length cs) -> len < 2 ^ 63 ->
  (forall a0' a2' a3' a4' : word,
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (len - 3)) a2' a3' a4' a5 a6 a7
                (Z_to_bv 64 0xf0) s3 s4 (Z_to_bv 64 (b2z (system_at (firstn (Z.to_nat len) cs))))
                s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1400c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (p + 1))
             a3 a4 a5 a6 a7 (Z_to_bv 64 0xf0) s3 s4 s5 s6 (Z_to_bv 64 0x13) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fd0) fc None m (seg_rom rsegs)).
Proof.
  intros cs p len Q ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HB HL HL63 K.
  rewrite <- (op4_sys_val cs len) in K by lia.
  replace (p + 1) with (p + 1 + 0) by lia.
  apply (op4_sys_loop cs p len Q ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           HB HL HL63 K (Z.to_nat (len - 3)) 0 a3 a4 s5); [lia | lia | lia | reflexivity].
Qed.

(* 0x1407c sext.w a6, s2;  0x14088 bltz a6: s2 = a position below 2^31 is not negative, s2 = 0xffffffff is -1 *)
Lemma op4_sextw_nonneg : forall v, 0 <= v < 2 ^ 31 ->
  bv_lts (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. rewrite bv_lts_zero_r, (unsigned_lit v), Z.add_0_r by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  rewrite unsigned_lit by lia. apply Z.leb_gt. lia.
Qed.

Lemma op4_lts_m1 : bv_lts (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = true.
Proof. rewrite bv_lts_zero_r, unsigned_lit_wrap. reflexivity. Qed.

(* ---------------------------------------------------------------- 0x14054: the queue search *)

(* The loop from position i: a0 = key (0x1400c lwu 0x6c(sp)), a1 = g_nq (0x14034 lwu 0xc(s9)), a2 = i, a3 = i + 1,
   a4 = &g_q[i] (0x14044 auipc + 0x14048 addi: 0x41558 = W_BASE_PLAIN + OFF_g_q), a5 = 0xffffffff (the -1 of no
   match yet; 0x1404c / 0x14050 at i = 0), s4 = &g_cmd (0x13e20 auipc + 0x13e2c addi: 0x37558 = W_BASE_PLAIN +
   OFF_g_cmd), s8 = 0x28 = Cmd_ESZ (0x13e24). The body is entered before the bound test (0x14070), so i < g_nq. *)
Lemma op4_find_scan : forall (B : list byte) (key : Z) (f : nat) (i at_ : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  wmem rsegs m B -> 0 <= key < 2 ^ 32 -> 0 <= i < g_nq B ->
  submit_find_at f B key i = Some at_ ->
  (forall a2' a3' a4' a5' a6' : word,
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 key) (Z_to_bv 64 (g_nq B)) a2' a3' a4' a5' a6' a7
                (Z_to_bv 64 (at_ mod 2 ^ 32)) s3 (Z_to_bv 64 0x37558) s5 s6 s7 (Z_to_bv 64 0x28)
                s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1408c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 key) (Z_to_bv 64 (g_nq B)) (Z_to_bv 64 i) (Z_to_bv 64 (i + 1))
             (Z_to_bv 64 (0x41558 + 4 * i)) (Z_to_bv 64 0xffffffff) a6 a7
             s2 s3 (Z_to_bv 64 0x37558) s5 s6 s7 (Z_to_bv 64 0x28) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14054) fc None m (seg_rom rsegs)).
Proof.
  intros B key f. induction f as [|f IH];
    intros i at_ Q ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m HWM HK Hi HF K;
    [cbn [submit_find_at] in HF; discriminate HF|].
  rewrite op4_find_step in HF.
  rewrite (proj2 (Z.ltb_lt i (g_nq B)) (proj2 Hi)) in HF.
  destruct (Z.leb_spec CMDS_MAX i) as [EI|EI]; [discriminate HF|].
  destruct (Z.leb_spec CMDS_MAX (Q_at B i)) as [EQ|EQ]; [discriminate HF|].
  unfold CMDS_MAX in EI, EQ.
  set (q := Q_at B i) in *.
  pose proof (u_at_range B (OFF_g_q + 4 * i) 4) as RQ. change (u_at B (OFF_g_q + 4 * i) 4) with q in RQ.
  pose proof (u_at_range B (A_Cmd_key q) 4) as RK. change (u_at B (A_Cmd_key q) 4) with (Cmd_key B q) in RK.
  pose proof (u_at_range B OFF_g_nq 4) as RN. change (u_at B OFF_g_nq 4) with (g_nq B) in RN.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RQ, RK, RN.
  (* g_q[i] at 0x41558 + 4 i, g_cmd[q].key at 0x37558 + 40 q + 4 (TWorld.v Q_at, A_Cmd_key) *)
  pose proof (wm_read rsegs W_BASE_PLAIN m B (OFF_g_q + 4 * i) 4 (Z_to_bv 64 (0x41558 + 4 * i)) HWM
                ltac:(unfold OFF_g_q; lia) ltac:(unfold OFF_g_q, W_LEN; lia)
                ltac:(f_equal; unfold W_BASE_PLAIN, OFF_g_q; lia)) as RDQ.
  pose proof (wm_read rsegs W_BASE_PLAIN m B (A_Cmd_key q) 4 (Z_to_bv 64 (0x37558 + q * 40 + 4)) HWM
                ltac:(unfold A_Cmd_key, OFF_g_cmd; lia) ltac:(unfold A_Cmd_key, OFF_g_cmd, W_LEN; lia)
                ltac:(f_equal; unfold W_BASE_PLAIN, A_Cmd_key, OFF_g_cmd; lia)) as RDK.
  (* ---- 0x14054 lwu a6, 0(a4) ---- *)
  step.
  change (u_at B (60872 + 4 * i) 4) with q.
  (* ---- 0x14058 mul a6, a6, s8;  0x1405c add a6, s4, a6 ---- *)
  step. zsimp. step. zsimp.
  (* ---- 0x14060 lwu a6, 4(a6) ---- *)
  step.
  change (u_at B (A_Cmd_key q) 4) with (Cmd_key B q).
  (* ---- 0x14064 mv s2, a2;  0x14068 beq a6, a0 -> 0x14070 ---- *)
  step. step.
  rewrite (op4_eqb_uu (Cmd_key B q) key) by lia.
  revert HF. destruct (Z.eqb_spec (Cmd_key B q) key) as [KM|KM]; cbv iota; intros HF.
  - (* g_cmd[g_q[i]].key == key: at = i *)
    injection HF as <-.
    (* 0x14070 bgeu a3, a1 -> 0x1408c *)
    step.
    rewrite (ltu_zz (i + 1) (g_nq B)) by lia.
    rewrite (Z.mod_small i (2 ^ 32)) in K by lia.
    destruct (Z.ltb_spec (i + 1) (g_nq B)) as [L|L]; cbn [negb].
    + (* 0x14074 .. 0x14088: the next turn is set up, but s2 = i is not negative: out *)
      do 6 step.
      rewrite (op4_sextw_nonneg i) by lia. cbv iota.
      apply K.
    + (* i + 1 >= g_nq: out at 0x1408c *)
      apply K.
  - (* no match at i: s2 keeps the -1 of a5 *)
    (* 0x1406c mv s2, a5;  0x14070 bgeu a3, a1 -> 0x1408c *)
    step. step.
    rewrite (ltu_zz (i + 1) (g_nq B)) by lia.
    destruct (Z.ltb_spec (i + 1) (g_nq B)) as [L|L]; cbn [negb].
    + (* 0x14074 .. 0x14088: s2 = 0xffffffff, sext.w is -1: back to 0x14054 at i + 1 *)
      do 6 step.
      rewrite op4_lts_m1. cbv iota.
      replace (i + 2) with (i + 1 + 1) by lia.
      replace (267608 + 4 * i + 4) with (0x41558 + 4 * (i + 1)) by lia.
      apply (IH (i + 1) at_ Q ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a7 (Z_to_bv 64 4294967295) s3 s5 s6 s7
               s9 s10 s11 t3 t4 t5 t6 F fc m HWM HK ltac:(lia) HF K).
    + (* the queue is exhausted: at = -1 *)
      assert (HA : at_ = -1).
      { destruct f as [|f']; [discriminate HF|].
        rewrite op4_find_step, (proj2 (Z.ltb_ge (i + 1) (g_nq B)) L) in HF.
        injection HF as <-. reflexivity. }
      rewrite HA in K. change (-1 mod 2 ^ 32) with 0xffffffff in K.
      apply K.
Qed.
