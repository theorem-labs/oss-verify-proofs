From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_count_c.
Import ListNotations.
Open Scope Z_scope.

(** check_count of the plain image (0x146b0, 12 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `addi a3, zero, -1`; `blt a0, a3` and `blt a1, a0` (rc < -1, cap < rc: the abort frame at 0x146d4, dead by
    -1 <= rc <= cap); `bltz a0` goes to the `ret` at 0x146d0 for rc = -1. For rc >= 0 the two `lw` read res->n and
    res->keys from the bytes_at premise (le4 rc, le4 keys); `lw` sign-extends, which is the identity on rc and keys
    (both in [0, 2^31)), so `bne a1, a0` (n <> rc) and `blt a1, a0` (keys < rc) are not taken, then `ret`. *)

(** The signed value of a 64-bit literal in the signed range. *)
Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (z mod 2^64 <? 2^63) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    Z.div_mod_to_equations; lia.
Qed.

(** `lw` sign-extends the low 32 bits: the identity on a 64-bit literal in the 32-bit signed range. *)
Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations; lia.
Qed.

(** A branch condition the premises refute. *)
Ltac kill K := exfalso; zify_cond K; rewrite ?signed_lit64 in K by lia; Z.div_mod_to_equations; lia.

Theorem check_count_holds : check_count_contract.
Proof.
  unfold check_count_contract, CHECK_COUNT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rc cap keys HA0 HA1 HRC HCAP HRES.
  subst a0 a1.
  (* addi a3, zero, -1 *)
  zstep.
  (* blt a0, a3: not taken, -1 <= rc *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ kill K | idtac ] .. ].
  (* blt a1, a0: not taken, rc <= cap *)
  zstep.
  let K := fresh "K" in
  if_cases K; [ first [ kill K | idtac ] .. ].
  (* bltz a0 *)
  zstep.
  if_cases KZ.
  - (* taken (rc = -1): ret *)
    zstep. finish.
  - (* not taken: 0 <= rc, the two words of res are rc and keys *)
    assert (Hpos : 0 <= rc) by (zify_cond KZ; rewrite ?signed_lit64 in KZ by lia; Z.div_mod_to_equations; lia).
    clear KZ.
    destruct (HRES Hpos) as [HB Hk]. clear HRES.
    pose proof (bytes_at_read rsegs m (bv_unsigned a2) _ 0 4 HB ltac:(lia)
                  ltac:(rewrite length_app, !length_le4; cbn; lia)) as R0.
    pose proof (bytes_at_read rsegs m (bv_unsigned a2) _ 4 4 HB ltac:(lia)
                  ltac:(rewrite length_app, !length_le4; cbn; lia)) as R1.
    change (firstn 4 (skipn (Z.to_nat 0) (le4 (Z_to_bv 64 rc) ++ le4 (Z_to_bv 64 keys))))
      with (le4 (Z_to_bv 64 rc)) in R0.
    change (firstn 4 (skipn (Z.to_nat 4) (le4 (Z_to_bv 64 rc) ++ le4 (Z_to_bv 64 keys))))
      with (le4 (Z_to_bv 64 keys)) in R1.
    (* the first load's address is a2 itself *)
    rewrite (wa_of_var a2 (bv_unsigned a2 + 0)) in R0 by lia.
    (* lw a1, 0(a2): a1 = rc *)
    zstep.
    rewrite (sx32_lit rc) by lia.
    (* bne a1, a0: not taken *)
    zstep.
    let K := fresh "K" in
    if_cases K; [ first [ kill K | idtac ] .. ].
    (* lw a1, 4(a2): a1 = keys *)
    zstep.
    rewrite (sx32_lit keys) by lia.
    (* blt a1, a0: not taken, rc <= keys; then ret *)
    zstep.
    let K := fresh "K" in
    if_cases K;
      first [ kill K
            | zstep; finish ].
Qed.
