From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Ltac cond_solve := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac ift := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; cond_solve] end.
Ltac iff_ := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; cond_solve] end.
Ltac st := first [step | ift | iff_].
Ltac run_to pc0 := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif constr_eq pc pc0 then fail else st
  | _ => st end).
Ltac norm_sum :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_swrap 32 ?e)] =>
      let z := eval vm_compute in (bv_swrap 32 e) in
      is_Zlit z; change (bv_swrap 32 e) with z
  end.

Lemma mulhu10 : forall X, 0 <= X < 256 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (X * 1844674407370955162) 64)) * 10)) = X - X mod 10.
Proof.
  intros X HX. rewrite Z.shiftr_div_pow2 by lia.
  assert (Q : X * 1844674407370955162 / 2 ^ 64 = X / 10) by (Z.div_mod_to_equations; lia).
  rewrite Q. rewrite (unsigned_lit (X / 10)) by (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia.
Qed.

Lemma remw_small : forall A n, 0 <= A < 256 -> 1 <= n <= 4 ->
  v_remw (Z_to_bv 64 A) (Z_to_bv 64 n) = Z_to_bv 64 (A mod n).
Proof.
  intros A n HA Hn. unfold v_remw. rewrite !unsigned_lit by lia.
  replace (bv_wrap 32 n =? 0) with false.
  2:{ symmetry. apply Z.eqb_neq. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
      rewrite Z.mod_small by lia. lia. }
  rewrite (swrap32_small A), (swrap32_small n) by lia. rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound A n ltac:(lia)). rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma beq_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_op : forall OP, 0 <= OP < 10 ->
  bv_ltu (Z_to_bv 64 (OP + -1)) (Z_to_bv 64 4) = (1 <=? OP) && (OP <=? 4).
Proof.
  intros OP H. assert (OP = 0 \/ OP = 1 \/ OP = 2 \/ OP = 3 \/ OP = 4 \/ OP = 5 \/ OP = 6 \/ OP = 7 \/ OP = 8 \/ OP = 9)
    as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]] by lia; reflexivity.
Qed.

Definition JTB : list byte := match image_bytes rsegs JT_BASE 36 with Some l => l | None => [] end.

Lemma jt_read : forall m c, bytes_at rsegs m JT_BASE JTB -> 0 <= c < 9 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (JT_BASE + 4 * c)) 4 = Some (firstn 4 (skipn (Z.to_nat (4 * c)) JTB)).
Proof.
  intros m c H Hc. change (Z_to_bv 64 (JT_BASE + 4 * c)) with (wa (JT_BASE + 4 * c)).
  apply bytes_at_read; [exact H | lia |]. change (length JTB) with 36%nat. lia.
Qed.

Ltac jt_case RJ :=
  lazymatch type of RJ with _ = Some ?l =>
    let l' := eval vm_compute in l in change l with l' in RJ end;
  unfold JT_BASE in RJ; cbn [Z.mul Z.add] in RJ;
  run_to 0x13ce4; step; apply evt_done; do 2 eexists; reflexivity.

Lemma djt : forall (OP : Z) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  bytes_at rsegs m JT_BASE JTB -> 0 <= OP < 10 ->
  evt rsegs (fun ms => exists a0 a1 : word,
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                   x28 x29 x30 x31) F (Z_to_bv 64 (jt_target OP)) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 OP) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
             x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13cc4) fc None m ro).
Proof.
  intros OP x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m ro JT HOP.
  assert (OP = 0 \/ OP = 1 \/ OP = 2 \/ OP = 3 \/ OP = 4 \/ OP = 5 \/ OP = 6 \/ OP = 7 \/ OP = 8 \/ OP = 9)
    as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]] by lia.
  - pose proof (jt_read m 0 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 1 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 2 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 3 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 4 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 5 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 6 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 7 JT ltac:(lia)) as RJ. jt_case RJ.
  - pose proof (jt_read m 8 JT ltac:(lia)) as RJ. jt_case RJ.
  - step. st. apply evt_done. do 2 eexists. reflexivity.
Qed.

Ltac split_rem :=
  lazymatch goal with |- context [Z_to_bv 64 (?A mod ?n)] =>
    let R := fresh "R" in let ER := fresh "ER" in
    remember (A mod n) as R eqn:ER;
    assert (0 <= R < n) by (subst R; apply Z.mod_pos_bound; lia);
    assert (R = 0 \/ R = 1 \/ R = 2 \/ R = 3) as [ -> |[ -> |[ -> | -> ]]] by lia; try lia
  end.

Ltac sel_A :=
  apply evt_done; do 9 eexists; split; [reflexivity|];
  split; [f_equal; lia|]; split; [f_equal; lia|]; left;
  split; [reflexivity|]; split; [reflexivity|];
  first [ exists 0%nat; split; [lia|]; split; reflexivity
        | exists 1%nat; split; [lia|]; split; reflexivity
        | exists 2%nat; split; [lia|]; split; reflexivity
        | exists 3%nat; split; [lia|]; split; reflexivity ].
Ltac sel_rest OP :=
  run_to 0x13c60; norm_sum; step; first [ift | iff_];
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 80996) _ _ _ _) =>
      step; rewrite remw_small by lia; split_rem; run_to 0x13cc4; sel_A
  | |- evt _ _ (MS _ _ (Z_to_bv 64 81040) _ _ _ _) =>
      step;
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        rewrite (beq_lit OP 1) by lia; destruct (OP =? 1) eqn:E1; cbn [negb]; cbv iota;
        [ apply Z.eqb_eq in E1; step; apply evt_done; do 9 eexists; split; [reflexivity|];
          split; [f_equal; lia|]; split; [f_equal; lia|]; right; left;
          split; [reflexivity|]; split; [exact E1|]; repeat split; reflexivity
        | apply Z.eqb_neq in E1; step; step; step; apply evt_done; do 9 eexists; split; [reflexivity|];
          split; [f_equal; lia|]; split; [f_equal; lia|]; right; right;
          split; [reflexivity|]; split; [exact E1|]; split; [f_equal; lia|]; split; [f_equal; lia|];
          repeat split; reflexivity ]
      end
  end.

Lemma dsel : forall (OP N K P SP f0 f1 f2 f3 : Z)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 ro : word -> option byte) (b1 : byte),
  (K + 1 < N -> ov_read_bytes rsegs m1 (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31044) 4 = Some (le4 (Z_to_bv 64 f0)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x310a4) 4 = Some (le4 (Z_to_bv 64 f1)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31104) 4 = Some (le4 (Z_to_bv 64 f2)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x31164) 4 = Some (le4 (Z_to_bv 64 f3)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (SP + 8)) 8 = Some (le8 (Z_to_bv 64 0x31040)) ->
  (f0 = 0 \/ f0 = 1) -> (f1 = 0 \/ f1 = 1) -> (f2 = 0 \/ f2 = 1) -> (f3 = 0 \/ f3 = 1) ->
  0 <= K < N -> N < 2 ^ 26 -> 0 <= OP < 10 ->
  evt rsegs (fun ms => exists (s0 s1 s2 s7 a1 a2 a3 a4 : word) (pc : Z),
      ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 s0 s1 (Z_to_bv 64 OP) a1 a2 a3 a4 (Z_to_bv 64 1) x16 x17 s2
                   x19 x20 x21 x22 s7 x24 x25 (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4) x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 ro /\
      s0 = Z_to_bv 64 (P + (if K + 1 <? N then K + 2 else K + 1)) /\
      s7 = Z_to_bv 64 (N - (if K + 1 <? N then K + 2 else K + 1)) /\
      ((pc = 0x13cc4 /\ s2 = Z_to_bv 64 (P + K) /\
        exists j, (j < 4)%nat /\ nth j [f0; f1; f2; f3] 0 = 1 /\ s1 = Z_to_bv 64 (0x31040 + 96 * Z.of_nat j)) \/
       (pc = 0x13c98 /\ OP = 1 /\ s1 = Z_to_bv 64 0 /\ s2 = Z_to_bv 64 (P + K) /\
        f0 = 0 /\ f1 = 0 /\ f2 = 0 /\ f3 = 0) \/
       (pc = 0x13d48 /\ OP <> 1 /\ s1 = Z_to_bv 64 (N - (if K + 1 <? N then K + 2 else K + 1)) /\
        s2 = Z_to_bv 64 (P + (if K + 1 <? N then K + 2 else K + 1)) /\ f0 = 0 /\ f1 = 0 /\ f2 = 0 /\ f3 = 0)))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K + 1)) (Z_to_bv 64 (N - K)) (Z_to_bv 64 OP) x11 x12
             x13 x14 (Z_to_bv 64 1) x16 x17 (Z_to_bv 64 (P + K)) x19 x20 x21 x22 (Z_to_bv 64 (N - K + -1)) x24 x25
             (Z_to_bv 64 0x31044) (Z_to_bv 64 0x311c4) x28 x29 x30 x31) F (Z_to_bv 64 0x13c30) fc None m1 ro).
Proof.
  intros OP N K P SP f0 f1 f2 f3 x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31
    F fc m1 ro b1 R1 F0 F1 F2 F3 RSP H0 H1 H2 H3 HK HN HOP.
  pose proof (bv_unsigned_in_range 8 b1) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
  destruct (Z.ltb_spec (K + 1) N) as [HKN|HKN].
  - specialize (R1 HKN). cbv iota. step. iff_. step. step. step. step.
    change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)).
    destruct H0 as [-> | ->]; destruct H1 as [-> | ->]; destruct H2 as [-> | ->]; destruct H3 as [-> | ->];
      sel_rest OP.
  - assert (K + 1 = N) by lia. cbv iota. step. ift. step.
    destruct H0 as [-> | ->]; destruct H1 as [-> | ->]; destruct H2 as [-> | ->]; destruct H3 as [-> | ->];
      sel_rest OP.
Qed.
