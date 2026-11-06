(* check_write (fuzz_link.c:568-577) and check_mark (:595-606), PLAIN build: the walks of their
   contracts (lib/Prog/check_write_c.v, check_rc_contract at CHECK_WRITE and at CHECK_MARK) on the
   plain image.

   The two functions are the same code at 0x15d58 and at 0x15e04, up to the pc-relative offset of
   the call to abort at +0x2c (jal 0x108c and jal 0xfe0, both to abort at 0x16e10), which the
   returning path does not execute. So the walk is ONE lemma, check_rc_walk, for any entry pc whose
   nine code words +0x00..+0x20 (the returning path) are those at CHECK_WRITE (`rc_code pc`). Each
   step reads the word at CHECK_WRITE + o from the image by computation, as `step` does, and
   `rc_code pc` carries it to pc + o; every branch and jump of the path is pc-relative, so nothing
   else depends on pc. `rc_code CHECK_WRITE` holds trivially and `rc_code CHECK_MARK` is checked
   word by word on the image.

   The returning path:
     +00 lui a2, 0xf4; +04 addiw a2, a2, 0x240            (a2 = 1000000 = RC_FAILS)
     +08 beq a1, a2, +0x10
       a1 = RC_FAILS:  +18 seqz a0, a0                     (a0 = (got == 0))
       a1 <> RC_FAILS: +0c xor a0, a0, a1; +10 snez a0, a0; +14 j +8   (a0 = (got != want))
     +1c bnez a0, +8                                       (to the abort path at +0x24)
     +20 ret
   same_rc_regs says the bnez is not taken: got <> 0 when want = RC_FAILS, got = want otherwise.
   Only a0 and a2 change; no memory is written. *)
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf hp_cka_kit check_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* the nine code words of the returning path at pc are those at CHECK_WRITE, in the image *)
Definition rc_code (pc : Z) : Prop :=
  forall k : nat, (k < 9)%nat ->
    fetch_word rsegs (Z_to_bv 64 (pc + 4 * Z.of_nat k)) =
    fetch_word rsegs (Z_to_bv 64 (CHECK_WRITE + 4 * Z.of_nat k)).

Lemma rc_fetch : forall pc o k w, rc_code pc -> (k < 9)%nat -> o = 4 * Z.of_nat k ->
  fetch_word rsegs (Z_to_bv 64 (CHECK_WRITE + o)) = Some w ->
  fetch_word rsegs (Z_to_bv 64 (pc + o)) = Some w.
Proof. intros pc o k w H Hk -> Hw. rewrite (H k Hk). exact Hw. Qed.

(* the offset o of a pc term `pc` or `pc + o` *)
Ltac rc_off pc e :=
  lazymatch e with
  | pc => constr:(0%Z)
  | Z.add pc ?o => o
  end.

(* `step` (lib/Lib/Step.v step_core) at pc + o: the word is fetched and decoded from the image at
   CHECK_WRITE + o by computation, and rc_code carries the fetch to pc + o *)
Ltac rc_step pc HC :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?e) ?fc ?rv ?m ?ro) =>
    let o := rc_off pc e in
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 (CHECK_WRITE + o))) in
    lazymatch fw with
    | Some ?w =>
      let ec := eval vm_compute in (is_ecall w) in
      lazymatch ec with
      | false =>
        let d := eval vm_compute in (decode_any w) in
        lazymatch d with
        | Some (?i, ?sz) =>
          let k := eval vm_compute in (Z.to_nat (o / 4)) in
          let HF := fresh "HF" in
          assert (HF : fetch_word segs (Z_to_bv 64 e) = Some w);
          [ first [ exact (rc_fetch pc o k w HC ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
                  | rewrite <- (Z.add_0_r pc);
                    exact (rc_fetch pc 0 0 w HC ltac:(lia) eq_refl ltac:(vm_compute; reflexivity)) ]
          | ];
          eapply evt_step;
          [ split; [reflexivity|];
            rewrite (step_gen segs R F (Z_to_bv 64 e) fc rv m ro w i sz HF) by (vm_compute; reflexivity);
            exec_pre i;
            exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
            try solve_load; try solve_store;
            reflexivity
          | clear HF; simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
        | None => fail "undecodable instruction at offset" o
        end
      | true => fail "ecall at offset" o
      end
    | None => fail "no instruction at offset" o
    end
  end.

Lemma check_rc_walk : forall pc, rc_code pc ->
  leaf_walk pc 0 (fun regs m => same_rc_regs regs) writes_nothing unchanged.
Proof.
  intros pc HC. unfold leaf_walk.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros HP MI ST LO SP.
  destruct HP as [H1 H2].
  change (a1 = wz RC_FAILS -> a0 <> wz 0) in H1.
  change (a1 <> wz RC_FAILS -> a0 = a1) in H2.
  rc_step pc HC. rc_step pc HC.
  (* beq a1, a2: a2 = RC_FAILS *)
  rc_step pc HC.
  if_cases K; zify_cond K; cbv iota.
  - (* want = RC_FAILS: got <> 0 *)
    assert (EA : a1 = wz RC_FAILS).
    { apply bv_eq. change (bv_unsigned (wz RC_FAILS)) with 1000000. lia. }
    pose proof (H1 EA) as NZ.
    assert (NZ' : bv_unsigned a0 <> 0).
    { intros E. apply NZ. apply bv_eq. rewrite E. reflexivity. }
    pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
    rc_step pc HC.
    rc_step pc HC.
    if_cases K2; zify_cond K2; cbv iota.
    + exfalso. lia.
    + rc_step pc HC.
      ret_unchanged MI ST.
  - (* want <> RC_FAILS: got = want *)
    assert (EA : a1 <> wz RC_FAILS).
    { intros E. subst a1. apply K. reflexivity. }
    pose proof (H2 EA) as E01. subst a0.
    rc_step pc HC. rewrite Z.lxor_nilpotent.
    rc_step pc HC. rc_step pc HC.
    rc_step pc HC. if_false.
    rc_step pc HC.
    ret_unchanged MI ST.
Qed.

Lemma check_rc_holds : forall pc, rc_code pc -> check_rc_contract pc.
Proof.
  intros pc HC. unfold check_rc_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in *. unfold same_rc_regs in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' _ _ H. exact H.
  - exact (check_rc_walk pc HC).
Qed.

Lemma rc_code_write : rc_code CHECK_WRITE.
Proof. intros k _. reflexivity. Qed.

(* check_mark's nine returning-path words, read from the image, are check_write's *)
Lemma rc_code_mark : rc_code CHECK_MARK.
Proof.
  intros k Hk.
  do 9 (destruct k as [|k]; [vm_compute; reflexivity|]).
  lia.
Qed.

Theorem check_write_holds : check_write_contract.
Proof. exact (check_rc_holds CHECK_WRITE rc_code_write). Qed.

Theorem check_mark_holds : check_mark_contract.
Proof. exact (check_rc_holds CHECK_MARK rc_code_mark). Qed.

Print Assumptions check_write_holds.
Print Assumptions check_mark_holds.
