(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma h413t_cell_amt : forall m DT dtb A, bytes_at usegs m DT dtb -> zlen dtb = 16388 -> huf_nb_ok false dtb 11 ->
  (A - DT - 4) mod 2 = 0 -> 0 <= A - DT - 4 < 4096 ->
  bv_unsigned (rdval usegs m (wa A) 2 false) mod 64 <= 11.
Proof.
  intros m DT dtb A DTB DL NB EV RG.
  set (X := (A - DT - 4) / 2).
  assert (HX : A = DT + (4 + 2 * X) /\ 0 <= X < 2048) by (subst X; Z.div_mod_to_equations; lia).
  destruct HX as [EA XB].
  destruct (NB X ltac:(change (2 ^ 11) with 2048; lia)) as (b & HB & HBV).
  change (if false then 4 * X + 6 else 2 * X + 4) with (2 * X + 4) in HB.
  rewrite EA.
  assert (HL : (Z.to_nat (2 * X + 4) < length dtb)%nat) by (apply (proj1 (nth_error_Some dtb _)); rewrite HB; discriminate).
  rewrite (rdval_bytes_at usegs m DT dtb (4 + 2 * X) 2 false DTB ltac:(lia) ltac:(lia)).
  unfold extz.
  assert (E2 : exists b2, firstn 2 (skipn (Z.to_nat (4 + 2 * X)) dtb) = [b; b2]).
  { replace (Z.to_nat (4 + 2 * X)) with (Z.to_nat (2 * X + 4)) by lia.
    pose proof HB as S0. rewrite <- (Nat.add_0_r (Z.to_nat (2 * X + 4))), <- nth_error_skipn in S0.
    destruct (skipn (Z.to_nat (2 * X + 4)) dtb) as [|x0 [|x1 rr]] eqn:ES; cbn in S0; [discriminate| |].
    - exfalso. assert (L : length (skipn (Z.to_nat (2 * X + 4)) dtb) = 1%nat) by (rewrite ES; reflexivity).
      rewrite skipn_length in L. lia.
    - injection S0 as E0. rewrite E0. exists x1. reflexivity. }
  destruct E2 as [b2 ->].
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (bv_unsigned_in_range 8 b) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
  unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 8) with 256 in R1, R2.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  clear - HBV R1 R2. Z.div_mod_to_equations. lia.
Qed.

Lemma h413t_amt_rde : forall m E DT dtb i X, bytes_at usegs m DT dtb -> zlen dtb = 16388 -> huf_nb_ok false dtb 11 ->
  0 <= DT /\ DT + 16388 < 2 ^ 64 -> ev E i = Z_to_bv 64 DT ->
  bv_unsigned (rdval usegs m (wa (estart E (SA (EAlu ALU_ADD (EVar i) (EMd M_MUL (ELit 2)
    (EAlu ALU_SRL (EAlu ALU_SRL X (ELit 52)) (ELit 1)))) 4))) 2 false) mod 64 <= 11.
Proof.
  intros m E DT dtb i X DTB DL NB [D0 D1] EI.
  unfold estart.
  change (bv_unsigned (rdval usegs m (wa (bv_unsigned (alu64 ALU_ADD (ev E i) (mul_div M_MUL (Z_to_bv 64 2)
    (alu64 ALU_SRL (alu64 ALU_SRL (edenot E X) (Z_to_bv 64 52)) (Z_to_bv 64 1)))) + 4)) 2 false) mod 64 <= 11).
  rewrite EI.
  pose proof (bv_unsigned_in_range 64 (edenot E X)) as RX. unfold bv_modulus in RX.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in RX.
  change (2 ^ 64) with 18446744073709551616 in D1.
  rewrite u_add64, u_mul64, u_srl64, u_srl64.
  change (2 ^ 64) with 18446744073709551616.
  rewrite !u_small by (change (2 ^ 64) with 18446744073709551616; lia).
  change (2 ^ (52 mod 64)) with 4503599627370496. change (2 ^ (1 mod 64)) with 2.
  set (q := bv_unsigned (edenot E X) / 4503599627370496 / 2).
  assert (Q : 0 <= q < 2048) by (subst q; clear - RX; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (2 * q)) by lia.
  rewrite (Z.mod_small (DT + 2 * q)) by lia.
  apply (h413t_cell_amt m DT dtb (DT + 2 * q + 4) DTB DL NB).
  - replace (DT + 2 * q + 4 - DT - 4) with (q * 2) by lia. apply Z.mod_mul. lia.
  - lia.
Qed.

Ltac h413t_ltn := apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity.

Ltac h413t_amt DTB DL NB11 DTR :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EVar ?j)) mod 64 <= 11 =>
      change (bv_unsigned (ev E j) mod 64 <= 11);
      lazymatch goal with
      | KXRD : reads_ok ?segs ?m ?nz0 ?reads E, KXA : atoms_ok ?zs E |- _ =>
          let nz := eval vm_compute in nz0 in
          let k := eval vm_compute in (j - nz)%nat in
          let r := eval vm_compute in (nth_error reads k) in
          lazymatch r with
          | Some (?a, ?n, ?sx) =>
              let H := fresh "RD" in
              pose proof (KXRD k a n sx ltac:(vm_cast_no_check (@eq_refl (option rdspec) (Some (a, n, sx))))) as H;
              change (ev E j = rdval segs m (wa (estart E a)) n sx) in H;
              rewrite H; clear H;
              eapply (h413t_amt_rde m E _ _ _ _ DTB DL NB11 DTR);
              rewrite (KXA _) by h413t_ltn; reflexivity
          end
      end
  | |- ?G => fail 1 "h413t_amt: unexpected amount" G
  end.

Ltac h413t_lb_atom KXA :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EVar ?a)) =>
      change (LBW p (ev E a)); rewrite (KXA a) by h413t_ltn; cbn [znth nth]; rewrite ?Z_to_bv_bv_unsigned;
      first [ assumption | lazymatch goal with |- ?G => fail 1 "h413t_lb_atom:" G end ]
  end.

Ltac h413t_lb_chain KXA DTB DL NB11 DTR :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL ?a ?b)) =>
      change (LBW p (alu64 ALU_SLL (edenot E a) (edenot E b)));
      let q := eval vm_compute in (p - 11) in
      change p with (q + 11);
      apply (lbw_sll q 11 (edenot E a) (edenot E b));
      [ h413t_lb_chain KXA DTB DL NB11 DTR | h413t_amt DTB DL NB11 DTR | clear; lia ]
  | |- LBW ?p (edenot ?E (EVar ?a)) => h413t_lb_atom KXA
  | |- ?G => fail 1 "h413t_lb_chain: unexpected goal" G
  end.

Ltac h413t_ctz DTB DL NB11 DTR :=
  match goal with
  | H : bv_unsigned (edenot ?E ?X) = 0, A : atoms_ok _ ?E |- _ =>
      lazymatch X with EAlu ALU_SLL _ _ => idtac end;
      let LW := fresh "LW" in
      assert (LW : LBW 63 (edenot E X)) by h413t_lb_chain A DTB DL NB11 DTR;
      exfalso; exact (lbw_nz _ _ LW H)
  end.
