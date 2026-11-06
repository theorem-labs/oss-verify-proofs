From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import check_object_c.
Import ListNotations.
Open Scope Z_scope.

(** check_object of the plain image (0x1473c, 17 instructions), walked with Lib/Tac.v and Lib/Step.v.
    `lw a2,0(a2)` reads x->rc = le4 (Z_to_bv 64 xrc), sign-extended (sx32, [co_sx32]); a3 = seqz (a0 + 1) is
    (rc = -1) on a0 = Z_to_bv 64 rc, a2 = sltiu a2, -1 is (xrc <> -1); `beq a3, a2` (to the abort frame at 0x14774)
    is not taken by the premise rc = -1 <-> xrc = -1. For rc <> -1 `bne a0, a2` goes to `ret`; for rc = -1 the
    three `lw` from res = ha_res_bytes 0 0 0 read 0, so no `bnez` is taken, then `ret`. *)

(** A 32-bit value read back by `lw` is the value itself. *)
Lemma co_sx32 : forall e, - 2 ^ 31 <= e < 2 ^ 31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in He. mlia.
Qed.

(** A branch whose taken side the context refutes: [if_cases], then the impossible side by [zify_cond] and
    [mlia] after a case split on each [Z.ltb] of the condition. *)
Ltac co_branch :=
  let K := fresh "K" in
  if_cases K;
    [ first [ exfalso; zify_cond K; revert K;
              repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
              cbn [Z.b2z]; intro K; mlia
            | idtac ] .. ].

Theorem check_object_holds : check_object_contract.
Proof.
  unfold check_object_contract, CHECK_OBJECT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rc xrc HA0 Hrc HX Hxrc HIFF HRES.
  subst a0.
  pose proof (bytes_at_read rsegs m (bv_unsigned a2) _ 0 4 HX ltac:(lia) ltac:(rewrite length_le4; lia)) as RX.
  change (firstn 4 (skipn (Z.to_nat 0) (le4 (Z_to_bv 64 xrc)))) with (le4 (Z_to_bv 64 xrc)) in RX.
  (* the load's address is a2 itself *)
  rewrite (wa_of_var a2 (bv_unsigned a2 + 0)) in RX by lia.
  clear HX.
  destruct (Z.eq_dec rc (-1)) as [Erc | Nrc].
  - (* rc = -1: x->rc = -1, and the three words of res are 0 *)
    pose proof (proj1 HIFF Erc) as Exrc.
    specialize (HRES Erc). clear HIFF. subst rc xrc.
    pose proof (bytes_at_read rsegs m (bv_unsigned a1) _ 0 4 HRES ltac:(lia)
                  ltac:(unfold ha_res_bytes; rewrite !length_app, !length_le4; cbn; lia)) as R0.
    pose proof (bytes_at_read rsegs m (bv_unsigned a1) _ 4 4 HRES ltac:(lia)
                  ltac:(unfold ha_res_bytes; rewrite !length_app, !length_le4; cbn; lia)) as R4.
    pose proof (bytes_at_read rsegs m (bv_unsigned a1) _ 8 4 HRES ltac:(lia)
                  ltac:(unfold ha_res_bytes; rewrite !length_app, !length_le4; cbn; lia)) as R8.
    change (firstn 4 (skipn (Z.to_nat 0) (ha_res_bytes 0 0 0))) with (le4 (Z_to_bv 64 0)) in R0.
    change (firstn 4 (skipn (Z.to_nat 4) (ha_res_bytes 0 0 0))) with (le4 (Z_to_bv 64 0)) in R4.
    change (firstn 4 (skipn (Z.to_nat 8) (ha_res_bytes 0 0 0))) with (le4 (Z_to_bv 64 0)) in R8.
    rewrite (wa_of_var a1 (bv_unsigned a1 + 0)) in R0 by lia.
    clear HRES.
    (* lw a2, 0(a2) *)
    zstep. rewrite co_sx32 by lia.
    (* addi a3, a0, 1; seqz a3, a3; sltiu a2, a2, -1 *)
    zstep. zstep. zstep.
    (* beq a3, a2: not taken *)
    zstep. co_branch.
    (* addi a2, zero, -1; bne a0, a2: not taken *)
    zstep. zstep. co_branch.
    (* lw a0, 0(a1); bnez a0: not taken *)
    zstep. rewrite co_sx32 by lia. zstep. co_branch.
    (* lw a0, 4(a1); bnez a0: not taken *)
    zstep. rewrite co_sx32 by lia. zstep. co_branch.
    (* lw a0, 8(a1); bnez a0: not taken *)
    zstep. rewrite co_sx32 by lia. zstep. co_branch.
    (* ret *)
    zstep. finish.
  - (* rc <> -1: x->rc <> -1 *)
    assert (Nx : xrc <> -1) by (intro E; apply Nrc, HIFF, E).
    clear HIFF HRES.
    (* lw a2, 0(a2) *)
    zstep. rewrite co_sx32 by lia.
    (* addi a3, a0, 1; seqz a3, a3; sltiu a2, a2, -1 *)
    zstep. zstep. zstep.
    (* beq a3, a2: not taken *)
    zstep. co_branch.
    (* addi a2, zero, -1; bne a0, a2: taken to the ret at 0x14770 *)
    zstep. zstep. co_branch.
    (* ret *)
    zstep. finish.
Qed.
