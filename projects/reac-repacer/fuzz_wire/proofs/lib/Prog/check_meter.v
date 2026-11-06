(* check_meter walk, fuzz_wire plain c8763dfc4e81 0x13048..0x13124 (fuzz_wire.c:100-131); new. rp_meter_counter is the
   named Section hypothesis HMC (its contract, rp_meter_counter_c.v), called at 0x130cc with &ctr = sp + 14 of
   check_meter's own 48-byte frame, which holds UNTOUCHED_CTR = 0xa5c3 (stored at 0x130c0). The harness computes eo
   (s1, 12 or 16) and want (s2) itself at 0x1305c..0x130b4; on every path they are meter_eo n bs and meter_ok n bs, so
   each abort() is unreachable:
   - 0x130d0 `bne a0, s2` -> 0x130f4: the post gives a0 = meter_ok ? 1 : 0 = s2.
   - 0x130f0 `beq a1, a0` -> 0x13104 (want): the post's memory is the 2-byte little-endian store of meter_value n bs at
     &ctr, so the `lhu` at 0x130d4 reads it back and it is f[eo + 2] | f[eo + 3] << 8, the value the harness builds at
     0x130e0..0x130ec.
   - 0x13100 `bne a0, a1` -> 0x130f4 (!want): the post leaves the memory, so the `lhu` reads UNTOUCHED_CTR back. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_meter_counter_c check_meter_c.
Import ListNotations.
Open Scope Z_scope.

Lemma meter_eo_16 : forall n bs, 13 < n -> meter_byte bs 12 = 0x81 -> meter_byte bs 13 = 0 -> meter_eo n bs = 16%nat.
Proof.
  intros n bs Hn H12 H13. unfold meter_eo. rewrite H12, H13, (proj2 (Z.ltb_lt _ _) Hn). reflexivity.
Qed.

Lemma meter_eo_12 : forall n bs, n <= 13 \/ meter_byte bs 12 <> 0x81 \/ meter_byte bs 13 <> 0 ->
  meter_eo n bs = 12%nat.
Proof.
  intros n bs H. unfold meter_eo. destruct H as [H|[H|H]].
  - rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r, andb_false_l. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

Lemma meter_ok_short : forall n bs, n < 1000 -> meter_ok n bs = false.
Proof.
  intros n bs Hn. unfold meter_ok. rewrite (proj2 (Z.leb_gt _ _) Hn), andb_false_r, !andb_false_l. reflexivity.
Qed.

Lemma meter_eo_cases : forall n bs, (meter_eo n bs = 12 \/ meter_eo n bs = 16)%nat.
Proof.
  intros n bs. unfold meter_eo.
  destruct ((13 <? n) && (meter_byte bs 12 =? 0x81) && (meter_byte bs 13 =? 0x00)); [right|left]; reflexivity.
Qed.

Lemma meter_ok_eo : forall n bs eo, meter_eo n bs = eo -> 1000 <= n ->
  meter_ok n bs = (meter_byte bs eo =? 0x88) && (meter_byte bs (eo + 1) =? 0x19).
Proof.
  intros n bs eo E Hn. unfold meter_ok. rewrite E.
  assert (H16 : (eo <= 16)%nat) by (destruct (meter_eo_cases n bs) as [H|H]; rewrite E in H; lia).
  rewrite (proj2 (Z.leb_le (Z.of_nat eo + 6) n)), (proj2 (Z.leb_le 1000 n)) by lia.
  reflexivity.
Qed.

Lemma meter_value_eo : forall n bs eo, meter_eo n bs = eo ->
  meter_value n bs = meter_byte bs (eo + 2) + 256 * meter_byte bs (eo + 3).
Proof. intros n bs eo E. unfold meter_value. rewrite E. reflexivity. Qed.

Lemma meter_value_range : forall n bs, 0 <= meter_value n bs < 2^16.
Proof.
  intros n bs. unfold meter_value, meter_byte.
  pose proof (byte_range (nth (meter_eo n bs + 2) bs (Z_to_bv 8 0))).
  pose proof (byte_range (nth (meter_eo n bs + 3) bs (Z_to_bv 8 0))). lia.
Qed.

Lemma zx16_lit : forall z, 0 <= z < 2^16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma wr_at_sub : forall m A n k j a, wr_at rsegs m A n -> 0 <= k -> k + j <= n -> a = A + k ->
  wr_at rsegs m a j.
Proof.
  intros m A n k j a (H0 & H1 & H) Hk Hj ->. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

(* `addi r, b, -c; seqz s, r` on a loaded byte b: s = (b == c). *)
Lemma chk_seqz_byte : forall (b : byte) c k, 0 <= c < 256 -> k = - c ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + k)) 1 = Z_to_bv 64 (if bv_unsigned b =? c then 1 else 0).
Proof.
  intros b c k Hc ->. pose proof (byte_range b) as Xb. unfold zxb. rewrite zxb_u.
  destruct (Z.eqb_spec (bv_unsigned b) c) as [E|E].
  - rewrite E. replace (c + - c) with 0 by lia. vm_compute. reflexivity.
  - unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + - c) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma chk_lor16 : forall x y : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x))
  = Z_to_bv 64 (bv_unsigned x + 256 * bv_unsigned y).
Proof.
  intros x y. apply bv_eq. rewrite lor_bytes16.
  pose proof (byte_range x). pose proof (byte_range y). rewrite unsigned_lit by lia. reflexivity.
Qed.

Ltac byte_cond H := zify_cond H; rewrite ?zxb_u in H.

(* Each byte test the model holds whose answer a path fixed. *)
Ltac eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.

Ltac meter_ok_is b :=
  lazymatch goal with Heo : meter_eo ?n ?bs = _ |- _ =>
    assert (Hok : meter_ok n bs = b)
      by (rewrite (meter_ok_eo n bs _ Heo ltac:(lia)); cbn [Nat.add]; unfold meter_byte; eqb_facts; reflexivity)
  end.

Section C.
Hypothesis HMC : rp_meter_counter_contract.

(* 0x130b8 (the `lui` of UNTOUCHED_CTR) .. 0x130d0, the call's return: 5 steps and rp_meter_counter's contract. *)
Ltac meter_call :=
  do 6 step;
  lazymatch goal with
  | FR : rw_cells _ ?mm ?A _ |- _ =>
    eapply evt_cut;
    [ eapply HMC;
      [ intros ?; split; [ | eassumption ]; lia
      | intros ?; lia
      | intros ?;
        let WFR := fresh "WFR" in
        pose proof (proj2 FR) as WFR; cbn [cells_size csize Nat.add] in WFR;
        rewrite unsigned_lit by lia;
        apply (wr_at_sub mm A 48 14 2); [ exact WFR | lia | lia | lia ] ]
    | ]
  end;
  intros ? (? & ? & ? & ? & ->);
  replace (ret_pc (Z_to_bv 64 78032)) with (Z_to_bv 64 78032) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

Ltac meter_epilogue sp :=
  do 6 step;
  apply evt_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- _ => release_frame FR ST (bv_unsigned sp) end;
  assumption.

(* want = 0: 0x130d0 `bne a0, s2` (both 0), then the `lhu` reads UNTOUCHED_CTR back from the frame slot the call left. *)
Ltac meter_tail_false sp :=
  meter_call;
  lazymatch goal with Hok : meter_ok _ _ = false |- _ => rewrite Hok end; cbv iota;
  step; if_false;
  step;
  rewrite (zx16_lit 42435) by lia;
  step; if_true;
  do 2 step;
  step; first [if_true | if_false];
  meter_epilogue sp.

(* want = 1: 0x130d0 `bne a0, s2` (both 1); the call stored meter_value at the frame slot, which the `lhu` reads back
   and 0x130dc..0x130ec rebuilds from f[eo + 2], f[eo + 3] (i2 / i3). *)
Ltac meter_tail_true i2 i3 sp :=
  meter_call;
  lazymatch goal with Hok : meter_ok _ _ = true |- _ => rewrite Hok end; cbv iota;
  replace (Z_to_bv 64 (bv_unsigned sp + -34)) with (wa (bv_unsigned sp + -48 + Z.of_nat 14))
    by (unfold wa; f_equal; lia);
  mem_after_store;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with BA : bytes_at _ mm _ ?bs |- _ =>
      let R2 := fresh "Ri2" in let R3 := fresh "Ri3" in
      pose proof (rd1 mm _ bs i2 BA ltac:(lia)) as R2;
      pose proof (rd1 mm _ bs i3 BA ltac:(lia)) as R3
    end
  end;
  step; if_false;
  step;
  rewrite (zx16_lit (meter_value _ _)) by apply meter_value_range;
  step; if_false;
  do 5 step;
  unfold zxb; rewrite !zxb_u, chk_lor16;
  lazymatch goal with Heo : meter_eo _ _ = _ |- _ => rewrite (meter_value_eo _ _ _ Heo) end;
  unfold meter_byte; cbn [Nat.add];
  step; first [if_true | if_false];
  meter_epilogue sp.

(* 0x13080 (the 1000-byte test) with s1 = eo and Heo : meter_eo n bs = eo; i0..i3 are eo, eo + 1, eo + 2, eo + 3. *)
Ltac meter_mid i0 i1 i2 i3 sp :=
  let H1000 := fresh "H1000" in let HB0 := fresh "HB0" in
  do 2 step; if_cases H1000;
  [ (* n < 1000: the meter declines *)
    zify_cond H1000;
    lazymatch goal with Heo : meter_eo ?n ?bs = _ |- _ =>
      assert (Hok : meter_ok n bs = false) by (apply meter_ok_short; lia) end;
    step; meter_tail_false sp
  | zify_cond H1000;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with BA : bytes_at _ mm _ ?bs |- _ =>
        let RB0 := fresh "RB0" in let RB1 := fresh "RB1" in
        pose proof (rd1 mm _ bs i0 BA ltac:(lia)) as RB0;
        pose proof (rd1 mm _ bs i1 BA ltac:(lia)) as RB1
      end
    end;
    do 4 step; if_cases HB0;
    [ (* f[eo] != 0x88 *)
      byte_cond HB0;
      first [ exfalso; lia
            | meter_ok_is false; step; meter_tail_false sp ]
    | byte_cond HB0;
      (* eo = 12 reached from f[12] = 0x81 cannot have f[12] = 0x88: that path is vacuous *)
      first
        [ exfalso; lia
        | do 3 step;
          rewrite (chk_seqz_byte _ 25 (-25)) by lia;
          lazymatch goal with Heo : meter_eo _ ?bs = _ |- _ =>
            destruct (Z.eqb_spec (bv_unsigned (nth i1 bs (Z_to_bv 8 0))) 25) as [E25|E25] end;
          [ meter_ok_is true; step; meter_tail_true i2 i3 sp
          | meter_ok_is false; step; meter_tail_false sp ] ] ] ].

Theorem check_meter_holds : check_meter_contract.
Proof.
  unfold check_meter_contract, CHECK_METER, CHECK_METER_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA ST HLO DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof BA as (B0 & B1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 8 step. if_cases HL.
  - (* n < 14: eo = 12, the meter declines *)
    zify_cond HL.
    assert (Heo : meter_eo (bv_unsigned a1) bs = 12%nat) by (apply meter_eo_12; left; lia).
    assert (Hok : meter_ok (bv_unsigned a1) bs = false) by (apply meter_ok_short; lia).
    do 3 step. meter_tail_false sp.
  - zify_cond HL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 12 BA ltac:(lia)) as R12; pose proof (rd1 mm _ bs 13 BA ltac:(lia)) as R13 end.
    change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
    do 3 step. if_cases H12.
    + (* f[12] != 0x81: eo = 12 *)
      byte_cond H12.
      assert (Heo : meter_eo (bv_unsigned a1) bs = 12%nat)
        by (apply meter_eo_12; right; left; unfold meter_byte; lia).
      step. meter_mid 12%nat 13%nat 14%nat 15%nat sp.
    + byte_cond H12. do 2 step. if_cases H13.
      * (* f[12] == 0x81 and f[13] == 0x00: the VLAN tag, eo = 16 *)
        byte_cond H13.
        assert (Heo : meter_eo (bv_unsigned a1) bs = 16%nat)
          by (apply meter_eo_16; [lia | unfold meter_byte; lia | unfold meter_byte; lia]).
        do 2 step. meter_mid 16%nat 17%nat 18%nat 19%nat sp.
      * (* f[13] != 0x00: eo = 12 *)
        byte_cond H13.
        assert (Heo : meter_eo (bv_unsigned a1) bs = 12%nat)
          by (apply meter_eo_12; right; right; unfold meter_byte; lia).
        step. meter_mid 12%nat 13%nat 14%nat 15%nat sp.
Qed.

End C.
