(* check_refusal_submit (fuzz/fuzz_transport.c:656-665), entry 0x16884, 40 instructions, FRAME 16.
   The machine walk of check_refusal_submit_c.v against the ubsan binary: the alignment trap of the
   member access (0x16884-0x16888), the inlined spec_system_at (spec.h:264-270) over c->bytes for
   c->len with the three pointer-overflow traps of its byte reads, then the two abort() tests of
   :663-664. Every trap and the abort are unreachable: the traps by cp + 32 <= 2^64 and cp mod 4 = 0,
   the aborts by exfalso from the model premise. The returning paths touch no stack (only the abort
   path has a prologue), so the memory is unchanged.
   The pure lemmas of the first section are build-independent and stand verbatim in the plain twin
   lib/Prog/T/check_refusal_submit.v (the two builds share no file: each Prog tree carries its own
   image Img0, rsegs and world base). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU TContract WMem check_refusal_submit_c.
Import ListNotations.
Open Scope Z_scope.

(* ==== build-independent: the model's byte reading, spec_system_at's loop, bv comparisons ==== *)

(* the model reads c as a list Z (zs c); the machine reads one byte at a time (u_at c k 1) *)
Lemma byte_at_zs : forall (l : list byte) (i : Z), byte_at (zs l) i = at8 l (Z.to_nat i).
Proof.
  intros l i. unfold byte_at, zs, at8, bz.
  change 0 with (bv_unsigned (b8 0)) at 1. apply map_nth.
Qed.

Lemma u_at_1 : forall (l : list byte) k, 0 <= k -> (Z.to_nat k < length l)%nat ->
  u_at l k 1 = at8 l (Z.to_nat k).
Proof.
  intros l k Hk Hl.
  assert (L1 : length (sub l k 1) = 1%nat) by (apply length_sub; lia).
  assert (NE : nth_error (sub l k 1) 0 = nth_error l (Z.to_nat k)).
  { rewrite (ne_sub l k 1%nat 0%nat Hk). cbn [Nat.ltb Nat.leb]. f_equal. lia. }
  destruct (sub l k 1) as [|x r] eqn:Es; [cbn in L1; lia|].
  cbn [nth_error] in NE.
  unfold u_at. rewrite Es.
  assert (R0 : r = []) by (destruct r; [reflexivity | cbn in L1; lia]). subst r.
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  unfold at8, bz. rewrite (nth_error_nth l (Z.to_nat k) (b8 0) (eq_sym NE)). reflexivity.
Qed.

Lemma u_at_1_lit : forall (l : list byte) (k : Z) (n : nat), Z.to_nat k = n -> 0 <= k ->
  (n < length l)%nat -> at8 l n = u_at l k 1.
Proof. intros l k n E Hk Hl. subst n. symmetry. apply u_at_1; assumption. Qed.

Lemma bzs_u : forall (l : list byte) (i : Z), 0 <= i -> (Z.to_nat i < length l)%nat ->
  byte_at (zs l) i = u_at l i 1.
Proof. intros l i Hi Hl. rewrite byte_at_zs. symmetry. apply u_at_1; assumption. Qed.

(* spec_system_at's loop (DgnSpec.v:256-269, spec.h:264-270): the three bytes it tests at i *)
Definition hit3 (b : list Z) (i : Z) : bool :=
  (byte_at b i =? 240) && (byte_at b (i + 1) =? SPEC_MAKER) && (byte_at b (i + 3) =? SPEC_FN_SYSTEM).

Lemma hit3_u : forall (l : list byte) i, 0 <= i -> (Z.to_nat (i + 3) < length l)%nat ->
  hit3 (zs l) i = (u_at l i 1 =? 240) && (u_at l (i + 1) 1 =? 19) && (u_at l (i + 3) 1 =? 112).
Proof. intros l i Hi Hl. unfold hit3. rewrite !bzs_u by lia. reflexivity. Qed.

(* the fuel is any number of iterations the loop can still run *)
Lemma sal_fuel : forall f1 f2 b len i, 0 <= i ->
  (Z.to_nat (len - i) <= f1)%nat -> (Z.to_nat (len - i) <= f2)%nat ->
  system_at_loop b len i f1 = system_at_loop b len i f2.
Proof.
  induction f1 as [|f1 IH]; intros f2 b len i Hi H1 H2.
  - destruct f2 as [|f2]; [reflexivity|].
    cbn [system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct f2 as [|f2].
    + cbn [system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + cbn [system_at_loop]. destruct (Z.ltb_spec (i + 3) len) as [L|L]; [|reflexivity].
      destruct ((byte_at b i =? 240) && (byte_at b (i + 1) =? SPEC_MAKER) && (byte_at b (i + 3) =? SPEC_FN_SYSTEM));
        [reflexivity|].
      apply IH; lia.
Qed.

(* i + 3 >= len: the C loop condition fails, the answer is -1 *)
Lemma sal_end : forall b len i f, ~ (i + 3 < len) -> system_at_loop b len i f = -1.
Proof.
  intros b len i f H. destruct f as [|f]; [reflexivity|].
  cbn [system_at_loop]. replace (i + 3 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* no F0 13 xx 70 at i: the loop goes on at i + 1 *)
Lemma sal_miss : forall b len i f, 0 <= i -> (Z.to_nat (len - i) <= f)%nat -> i + 3 < len ->
  hit3 b i = false -> system_at_loop b len i f = system_at_loop b len (i + 1) f.
Proof.
  intros b len i f Hi Hf Hlt Hm. destruct f as [|f]; [cbn in Hf; lia|].
  rewrite (sal_fuel (S f) f b len (i + 1)) by lia.
  cbn [system_at_loop]. replace (i + 3 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold hit3 in Hm. rewrite Hm. reflexivity.
Qed.

(* F0 13 xx 70 at i: the loop answers i *)
Lemma sal_hit : forall b len i f, (Z.to_nat (len - i) <= f)%nat -> i + 3 < len ->
  hit3 b i = true -> system_at_loop b len i f = i.
Proof.
  intros b len i f Hf Hlt Hm. destruct f as [|f]; [cbn in Hf; lia|].
  cbn [system_at_loop]. replace (i + 3 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold hit3 in Hm. rewrite Hm. reflexivity.
Qed.

(* bltu / bgeu / beq / bne of two Z values in a register *)
Lemma ltu_zz : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_ss : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply Hne. revert E. Z.div_mod_to_equations. lia.
Qed.

(* the two bit operations of the ubsan prologue, in the shape step leaves: the alignment test
   (andi a3,a0,3) and ~c (not a4,a0 = xori a4,a0,-1) *)
Lemma and3_lit : forall x, 0 <= x < 2 ^ 64 -> x mod 4 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
Proof.
  intros x Hx H4. rewrite unsigned_lit by lia.
  replace 3 with (Z.ones 2) by (vm_compute; reflexivity).
  rewrite Z.land_ones by lia. replace (2 ^ 2) with 4 by (vm_compute; reflexivity).
  rewrite H4. reflexivity.
Qed.

Lemma not_lit : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. rewrite unsigned_lit by lia.
  rewrite zb_lxor_ones by lia. f_equal.       (* f_equal closes it: 2 ^ 64 - 1 is that literal *)
Qed.

(* a one-byte read of the argument block *)
Lemma rd1 : forall m p (l : list byte) k, bytes_at rsegs m p l -> 0 <= k ->
  (Z.to_nat k + 1 <= length l)%nat -> ov_read_bytes rsegs m (wa (p + k)) 1 = Some (sub l k 1).
Proof. intros m p l k H Hk Hn. apply (bytes_at_read rsegs m p l k 1%nat); assumption. Qed.

(* ==== the walk ==== *)

Theorem check_refusal_submit_holds : check_refusal_submit_contract.
Proof.
  unfold check_refusal_submit_contract, check_refusal_submit_FRAME, check_refusal_submit_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' cp c rc before.
  intros A0 A1 A2 RCr BFr CPp CP4 HC LC OW WM HM SP16 ST LO WOFF MI.
  subst a0 a1 a2.
  unfold off_window in OW. unfold w_off_stack in WOFF.
  wk_facts.
  pose proof (bytes_at_bound rsegs m cp c HC) as CB0. rewrite LC in CB0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  (* the model: length c = 32 closes the first guard; the second gives c->len <= 32 *)
  unfold check_refusal_submit_m in HM. rewrite LC in HM. cbn [Nat.ltb Nat.leb orb] in HM.
  rewrite (u_at_1_lit c 24 24%nat ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite LC; lia)) in HM.
  pose proof (u_at_range c 24 1) as LR. cbn [Z.of_nat] in LR.
  destruct (Z.ltb_spec (Z.of_nat 32) (u_at c 24 1)) as [LH|LH]; cbn [orb] in HM; [discriminate HM|].
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.

  (* the epilogue: one ret, no stack *)
  assert (EPI : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evt rsegs QQ
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x168fc) fc None m (seg_rom rsegs))).
  { intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    step.                                        (* 168fc ret *)
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact MI|]. split; [exact ST|].
    split; [|exact WM].
    revert HM. destruct (if 0 <=? spec_system_at (zs c) (u_at c 24 1)
                         then negb (rc =? SPEC_E_REFUSED) || negb (S_queued B =? before)
                         else rc =? SPEC_E_REFUSED);
      intros HM; congruence. }

  step.                                          (* 16884 andi a3,a0,3 *)
  rewrite (and3_lit cp) by lia.
  step.                                          (* 16888 bnez a3 -> 16920 (unimp) *)
  rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  pose proof (rd1 m cp c 24 HC ltac:(lia) ltac:(rewrite LC; lia)) as RD24.
  step.                                          (* 1688c lbu a6,24(a0) *)
  rewrite (wm_lbu c 24).
  set (len := u_at c 24 1) in *.
  assert (LEN : 0 <= len < 256) by (unfold len; cbn in LR; lia).
  assert (LEN32 : len <= 32) by (unfold len; cbn in LH; lia).
  do 2 step.                                     (* 16890 li a3,4 ; 16894 bltu a6,a3 -> 168f4 *)
  rewrite (ltu_zz len 4) by lia.
  destruct (Z.ltb_spec len 4) as [L4|L4]; cbv iota.
  - (* c->len < 4: the C loop never runs, spec_system_at = -1 *)
    assert (SA : spec_system_at (zs c) len = -1).
    { unfold spec_system_at. apply sal_end. lia. }
    rewrite SA in HM. cbn [Z.leb] in HM.
    do 2 step.                                   (* 168f4 li a0,-10 ; 168f8 beq a1,a0 -> 16914 *)
    rewrite (eqb_ss rc (-10)) by lia.
    destruct (Z.eqb_spec rc (-10)) as [E10|E10]; cbv iota.
    + exfalso. revert HM. unfold SPEC_E_REFUSED. rewrite E10. cbn. discriminate.
    + apply EPI.
  - (* c->len >= 4: the loop, i = 0 .. c->len - 4 *)
    assert (LOOP : forall (k : nat) (i : Z) (x28 : word),
      Z.of_nat k = len - 3 - i -> 0 <= i -> i + 3 < len ->
      system_at_loop (zs c) len i (Z.to_nat len) = spec_system_at (zs c) len ->
      evt rsegs QQ
        (MS (mkR ra sp gp tp (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) s0 s1
                 (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                 (Z_to_bv 64 i) (Z_to_bv 64 (2 ^ 64 - 1 - cp)) (Z_to_bv 64 (cp + 3))
                 (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (cp + 1))
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
            F (Z_to_bv 64 0x168b8) fc None m (seg_rom rsegs))).
    { induction k as [|k IH]; intros i x28 Hk Hi Hlt INV; [lia|].
      pose proof (rd1 m cp c i HC ltac:(lia) ltac:(rewrite LC; lia)) as RDi.
      pose proof (rd1 m cp c (i + 1) HC ltac:(lia) ltac:(rewrite LC; lia)) as RDi1.
      pose proof (rd1 m cp c (i + 3) HC ltac:(lia) ltac:(rewrite LC; lia)) as RDi3.
      pose proof (u_at_range c i 1) as Ri. cbn [Z.of_nat] in Ri.
      pose proof (u_at_range c (i + 1) 1) as Ri1. cbn [Z.of_nat] in Ri1.
      pose proof (u_at_range c (i + 3) 1) as Ri3. cbn [Z.of_nat] in Ri3.
      assert (HU : hit3 (zs c) i =
                   (u_at c i 1 =? 240) && (u_at c (i + 1) 1 =? 19) && (u_at c (i + 3) 1 =? 112))
        by (apply hit3_u; [lia | rewrite LC; lia]).
      (* the loop's three byte tests, each behind its pointer-overflow trap *)
      step.                                      (* 168b8 bltu a4,a3 -> 16920 *)
      rewrite (ltu_zz (2 ^ 64 - 1 - cp) i) by lia.
      replace (2 ^ 64 - 1 - cp <? i) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      do 2 step.                                 (* 168bc add t3,a0,a3 ; 168c0 lbu t3,0(t3) *)
      rewrite (wm_lbu c i).
      step.                                      (* 168c4 bne t3,t0 -> 168ec *)
      rewrite (eqb_ss (u_at c i 1) 240) by lia.
      assert (NEXT : forall (y28 : word), hit3 (zs c) i = false ->
        evt rsegs QQ
          (MS (mkR ra sp gp tp (Z_to_bv 64 240) (Z_to_bv 64 19) (Z_to_bv 64 112) s0 s1
                   (Z_to_bv 64 cp) (Z_to_bv 64 rc) (Z_to_bv 64 (bv_swrap 32 before))
                   (Z_to_bv 64 i) (Z_to_bv 64 (2 ^ 64 - 1 - cp)) (Z_to_bv 64 (cp + 3))
                   (Z_to_bv 64 (len - 3)) (Z_to_bv 64 (cp + 1))
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
              F (Z_to_bv 64 0x168ec) fc None m (seg_rom rsegs))).
      { intros y28 MISS.
        step.                                    (* 168ec addi a3,a3,1 *)
        step.                                    (* 168f0 bne a6,a3 -> 168b8 *)
        rewrite (eqb_ss (len - 3) (i + 1)) by lia.
        destruct (Z.eqb_spec (len - 3) (i + 1)) as [Z0|Z0]; cbn [negb].
        - (* the loop is done: i was c->len - 4, so the answer is -1 *)
          assert (SA : spec_system_at (zs c) len = -1).
          { rewrite <- INV. rewrite (sal_miss (zs c) len i (Z.to_nat len) ltac:(lia) ltac:(lia) Hlt MISS).
            apply sal_end. lia. }
          rewrite SA in HM. cbn [Z.leb] in HM.
          do 2 step.                             (* 168f4 li a0,-10 ; 168f8 beq a1,a0 *)
          rewrite (eqb_ss rc (-10)) by lia.
          destruct (Z.eqb_spec rc (-10)) as [E10|E10]; cbv iota.
          + exfalso. revert HM. unfold SPEC_E_REFUSED. rewrite E10. cbn. discriminate.
          + apply EPI.
        - apply (IH (i + 1)); try lia.
          rewrite <- INV. symmetry.
          apply (sal_miss (zs c) len i (Z.to_nat len)); [lia | lia | lia | exact MISS]. }
      destruct (Z.eqb_spec (u_at c i 1) 240) as [B0|B0]; cbn [negb].
      2: { apply NEXT. rewrite HU.
           replace (u_at c i 1 =? 240) with false by (symmetry; apply Z.eqb_neq; exact B0). reflexivity. }
      step.                                      (* 168c8 bgeu a3,a4 -> 16920 *)
      rewrite (ltu_zz i (2 ^ 64 - 1 - cp)) by lia.
      replace (i <? 2 ^ 64 - 1 - cp) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
      do 2 step.                                 (* 168cc add t3,a7,a3 ; 168d0 lbu t3,0(t3) *)
      rewrite (wm_lbu c (i + 1)).
      step.                                      (* 168d4 bne t3,t1 -> 168ec *)
      rewrite (eqb_ss (u_at c (i + 1) 1) 19) by lia.
      destruct (Z.eqb_spec (u_at c (i + 1) 1) 19) as [B1|B1]; cbn [negb].
      2: { apply NEXT. rewrite HU.
           replace (u_at c i 1 =? 240) with true by (symmetry; apply Z.eqb_eq; exact B0).
           replace (u_at c (i + 1) 1 =? 19) with false by (symmetry; apply Z.eqb_neq; exact B1). reflexivity. }
      do 2 step.                                 (* 168d8 addi t3,a3,3 ; 168dc bltu a4,t3 -> 16920 *)
      rewrite (ltu_zz (2 ^ 64 - 1 - cp) (i + 3)) by lia.
      replace (2 ^ 64 - 1 - cp <? i + 3) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      do 2 step.                                 (* 168e0 add t3,a5,a3 ; 168e4 lbu t3,0(t3) *)
      rewrite (wm_lbu c (i + 3)).
      step.                                      (* 168e8 beq t3,t2 -> 16900 *)
      rewrite (eqb_ss (u_at c (i + 3) 1) 112) by lia.
      destruct (Z.eqb_spec (u_at c (i + 3) 1) 112) as [B3|B3]; cbv iota.
      2: { apply NEXT. rewrite HU.
           replace (u_at c i 1 =? 240) with true by (symmetry; apply Z.eqb_eq; exact B0).
           replace (u_at c (i + 1) 1 =? 19) with true by (symmetry; apply Z.eqb_eq; exact B1).
           replace (u_at c (i + 3) 1 =? 112) with false by (symmetry; apply Z.eqb_neq; exact B3). reflexivity. }
      (* a hit at i: the model's spec_system_at is i >= 0, so the command is of the system family *)
      assert (SA : spec_system_at (zs c) len = i).
      { rewrite <- INV. apply sal_hit; [lia | lia|]. rewrite HU.
        replace (u_at c i 1 =? 240) with true by (symmetry; apply Z.eqb_eq; exact B0).
        replace (u_at c (i + 1) 1 =? 19) with true by (symmetry; apply Z.eqb_eq; exact B1).
        replace (u_at c (i + 3) 1 =? 112) with true by (symmetry; apply Z.eqb_eq; exact B3). reflexivity. }
      rewrite SA in HM.
      replace (0 <=? i) with true in HM by (symmetry; apply Z.leb_le; lia).
      do 2 step.                                 (* 16900 li a0,-10 ; 16904 bne a1,a0 -> 16914 *)
      rewrite (eqb_ss rc (-10)) by lia.
      destruct (Z.eqb_spec rc (-10)) as [E10|E10]; cbn [negb].
      2: { exfalso. revert HM. unfold SPEC_E_REFUSED.
           replace (rc =? -10) with false by (symmetry; apply Z.eqb_neq; exact E10). cbn. discriminate. }
      assert (QEQ : S_queued B = before).
      { revert HM. unfold SPEC_E_REFUSED. rewrite E10. cbn [Z.eqb negb orb].
        destruct (Z.eqb_spec (S_queued B) before) as [Q|Q]; [intros _; exact Q | cbn; discriminate]. }
      do 2 step.                                 (* 16908 auipc a0,0x21 ; 1690c lw a0,1864(a0) *)
      change (s32_at B 19792) with (s32_at B A_S_queued).
      unfold s32_at. fold (S_queued B). rewrite QEQ.
      step.                                      (* 16910 beq a0,a2 -> 168fc *)
      rewrite bv_eqb_refl. cbv iota.
      apply EPI. }
    do 8 step.                                   (* 16898 .. 168b4: the loop's set-up *)
    rewrite (not_lit cp) by lia.
    apply (LOOP (Z.to_nat (len - 3)) 0); try lia.
    reflexivity.
Qed.
