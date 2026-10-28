(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kx_clear_or2 := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
Ltac kx_lia1 := kx_clear_or2; kx_bv_ranges; lia.

(* [comment removed for export] *)
Ltac kx_rr_loop segs m E KXRD nz reads k :=
  lazymatch reads with
  | @nil _ => idtac
  | @cons _ (?a, ?n, ?sx) ?rest =>
      lazymatch sx with
      | false =>
          let small := eval vm_compute in (Nat.ltb n 8) in
          lazymatch small with
          | true =>
              let j := eval vm_compute in (nz + k)%nat in
              lazymatch goal with
              | _ : 0 <= bv_unsigned (ev E j) <= _ |- _ => idtac
              | _ =>
                  let hi := eval vm_compute in (2 ^ (8 * Z.of_nat n) - 1) in
                  let HR := fresh "KXRR" in
                  try assert (HR : 0 <= bv_unsigned (ev E j) <= hi)
                    by (let X := fresh in
                        pose proof (KXRD k a n false ltac:(reflexivity)) as X;
                        change (ev E j = rdval segs m (adenot E a) n false) in X;
                        rewrite X; exact (rdval_range segs m _ n ltac:(vm_compute; lia)))
              end
          | false => idtac
          end
      | true => idtac
      end;
      let k' := eval vm_compute in (S k) in
      kx_rr_loop segs m E KXRD nz rest k'
  end.
Ltac kx_rr_dedup :=
  try match goal with
      | KXRD : reads_ok ?segs ?m ?nz ?reads ?E |- _ => kx_rr_loop segs m E KXRD nz reads 0%nat
      end.

(* [comment removed for export] *)
Ltac kx_path_hyp_fast E zs nz KXA BR :=
  lazymatch type of BR with
  | branch_taken ?c (edenot E ?a) (edenot E ?b) = ?t =>
      lazymatch c with
      | BC_LT => idtac | BC_GE => idtac
      | _ =>
          let ua := kx_uz E zs nz a in
          let ub := kx_uz E zs nz b in
          let BR' := fresh "KXBR" in
          pose proof (br_propu_ok c t _ _ BR) as BR';
          rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA) in BR';
          change (br_propu c t ua ub) in BR';
          cbv beta iota delta [br_propu] in BR';
          rewrite ?kx_umod in BR';
          repeat match type of BR' with
                 | context [?z mod 2^64] =>
                     let HR := fresh "KXBRr" in
                     first [ assert (HR : 0 <= z < 2^64) by (clear BR'; kx_lia1);
                             rewrite (Z.mod_small z (2^64) HR) in BR'; clear HR
                           | assert (HR : 0 <= z < 2^64) by kx_lia1;
                             rewrite (Z.mod_small z (2^64) HR) in BR' ]
                 end;
          clear BR
      end
  end;
  lazymatch goal with
  | BR0 : branch_taken ?c (edenot E ?a) (edenot E ?b) = ?t |- _ =>
      let za := kx_ez E zs nz a in
      let zb := kx_ez E zs nz b in
      let BR' := fresh "KXBR" in
      assert (BR' : branch_taken c (Z_to_bv 64 za) (Z_to_bv 64 zb) = t)
        by (change (branch_taken c (Z_to_bv 64 (ez E zs a)) (Z_to_bv 64 (ez E zs b)) = t);
            rewrite <- (ez_sound zs E a KXA), <- (ez_sound zs E b KXA); exact BR0);
      clear BR0;
      cbn [branch_taken] in BR';
      try zify_cond BR';
      repeat match type of BR' with
             | context [bv_signed (Z_to_bv 64 ?z)] =>
                 let HS := fresh "KXBRs" in
                 assert (HS : 0 <= z < 2^63) by (clear BR'; kx_lia1);
                 rewrite (kx_signed_small z HS) in BR'; clear HS
             end
  | _ => idtac
  end.
