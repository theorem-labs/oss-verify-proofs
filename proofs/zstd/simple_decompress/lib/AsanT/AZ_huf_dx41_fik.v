(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AZ_huf_iface AZ_huf_lbkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma x1cell_amt : forall m DT dtb A, bytes_at bsegs m DT dtb -> zlen dtb = 16388 -> huf_nb_ok false dtb 11 ->
  (A - DT - 4) mod 2 = 0 -> 0 <= A - DT - 4 < 4096 ->
  bv_unsigned (rdval bsegs m (wa A) 2 false) mod 64 <= 11.
Proof.
  intros m DT dtb A DTB DL NB EV RG.
  set (X := (A - DT - 4) / 2).
  assert (HX : A = DT + (4 + 2 * X) /\ 0 <= X < 2048) by (subst X; Z.div_mod_to_equations; lia).
  destruct HX as [EA XB].
  destruct (NB X ltac:(change (2 ^ 11) with 2048; lia)) as (b & HB & HBV).
  change (if false then 4 * X + 6 else 2 * X + 4) with (2 * X + 4) in HB.
  rewrite EA.
  assert (HL : (Z.to_nat (2 * X + 4) < length dtb)%nat) by (apply (proj1 (nth_error_Some dtb _)); rewrite HB; discriminate).
  rewrite (rdval_bytes_at bsegs m DT dtb (4 + 2 * X) 2 false DTB ltac:(lia) ltac:(lia)).
  unfold extz.
  assert (E2 : exists b2, firstn 2 (skipn (Z.to_nat (4 + 2 * X)) dtb) = [b; b2]).
  { replace (Z.to_nat (4 + 2 * X)) with (Z.to_nat (2 * X + 4)) by lia.
    pose proof HB as S0. rewrite <- (Nat.add_0_r (Z.to_nat (2 * X + 4))), <- nth_error_skipn in S0.
    destruct (skipn (Z.to_nat (2 * X + 4)) dtb) as [|x0 [|x1 r]] eqn:ES; cbn in S0; [discriminate| |].
    - exfalso. assert (L : length (skipn (Z.to_nat (2 * X + 4)) dtb) = 1%nat) by (rewrite ES; reflexivity).
      rewrite skipn_length in L. lia.
    - injection S0 as ->. exists x1. reflexivity. }
  destruct E2 as [b2 ->].
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (bv_unsigned_in_range 8 b) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
  unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 8) with 256 in R1, R2.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  clear - HBV R1 R2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac fik_amt_fact j DTB DL NB11 :=
  let H := fresh "RD" in
  kx_read_eq j H;
  lazymatch type of H with
  | ev ?E j = rdval bsegs ?m (wa ?A) 2 false =>
      let F := fresh "HAMT" in
      assert (F : bv_unsigned (ev E j) mod 64 <= 11)
        by (rewrite H; apply (x1cell_amt m _ _ A DTB DL NB11); [clear; Z.div_mod_to_equations; lia | clear; Z.div_mod_to_equations; lia]);
      clear H
  | _ => clear H
  end.
Ltac fik_amt_loop j k DTB DL NB11 :=
  lazymatch k with
  | O => idtac
  | S ?k' => try (fik_amt_fact j DTB DL NB11); fik_amt_loop (S j) k' DTB DL NB11
  end.
(* [comment removed for export] *)
Ltac fik_amt_all DTB DL NB11 :=
  lazymatch goal with
  | KXRD : reads_ok _ _ ?nz ?reads _ |- _ =>
      let k := eval vm_compute in (length reads) in
      fik_amt_loop nz k DTB DL NB11
  end.

(* [comment removed for export] *)
Ltac fik_atom_eq c :=
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- _ =>
      let rec find l i := lazymatch l with
                          | (bv_unsigned c) :: _ => constr:(i)
                          | _ :: ?l' => find l' (S i)
                          end in
      let a := find zs O in
      let F := fresh "HATOM" in
      assert (F : ev E a = c) by (rewrite (KXA a) by (cbn [length]; lia); cbn [znth nth]; apply Z_to_bv_bv_unsigned)
  end.

(* [comment removed for export] *)
Ltac fik_lbw_cell X P W :=
  lazymatch X with
  | edenot ?E (EAlu ALU_SLL (EVar ?a) (EVar ?j)) =>
      set (W := X) in *;
      let L := fresh "HLBN" in
      assert (L : LBW P W)
        by (subst W; change (LBW P (alu64 ALU_SLL (ev E a) (ev E j)));
            lazymatch goal with
            | HA : ev E a = ?c, HC : LBW ?p ?c, HM : bv_unsigned (ev E j) mod 64 <= 11 |- _ =>
                rewrite HA; replace P with (p + 11) by reflexivity; apply (lbw_sll p 11); [exact HC | exact HM | clear; lia]
            end);
      clearbody W
  | _ => fail 100 "fik_lbw_cell: unexpected container term" X
  end.
(* [comment removed for export] *)
Ltac fik_lbw_cells P :=
  lazymatch goal with
  | LCB : rw_cells bsegs ?m (?SPV + -144) [C8 ?X0; C8 ?X1; C8 ?X2; C8 ?X3; _] |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      let W0 := fresh "W0" in let W1 := fresh "W1" in let W2 := fresh "W2" in let W3 := fresh "W3" in
      fik_lbw_cell X0 P W0; fik_lbw_cell X1 P W1; fik_lbw_cell X2 P W2; fik_lbw_cell X3 P W3
  end.
