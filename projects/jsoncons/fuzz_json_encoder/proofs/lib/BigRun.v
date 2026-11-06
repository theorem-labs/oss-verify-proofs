(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import BigModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sso_max : nat := 22%nat.
Definition str_alloc_bytes (n : nat) : Z :=
  if (n =? 23)%nat then 26 else Z.lor (Z.of_nat n) 7 + 1.

Record outcome := Outcome {
  o_events : list event;       (* [comment removed for export] *)
  o_thrown : option exn;       (* [comment removed for export] *)
  o_b : option sto;            (* [comment removed for export] *)
  o_c : option sto;            (* [comment removed for export] *)
  o_d : option sto             (* [comment removed for export] *)
}.

Definition harness_body (p : list Z) : M (option exn * option sto * option sto * option sto) :=
  if (length p <? 5000)%nat then
    do ra <- to_bigint lit_a sto_empty ;                      (* [comment removed for export] *)
    match ra with
    | ParseErr => ret (None, None, None, None)                (* [comment removed for export] *)
    | ParseOk a =>
      do rb <- to_bigint p sto_empty ;                        (* [comment removed for export] *)
      match rb with
      | ParseErr =>
          (* [comment removed for export] *)
          emit (EThrow SystemError22) ;; destroy a ;; emit ECatch ;;
          ret (Some SystemError22, None, None, None)
      | ParseOk b =>
          do x <- copy a ;                                    (* [comment removed for export] *)
          do m1 <- mod_assign x b ;                           (* [comment removed for export] *)
          match m1 with
          | ModZero =>
              (* [comment removed for export] *)
              destroy x ;; destroy b ;; destroy a ;; emit ECatch ;;
              ret (Some ZeroDivide, Some b, None, None)
          | ModAssert xc =>
              (* [comment removed for export] *)
              destroy xc ;; destroy b ;; destroy a ;; emit ECatch ;;
              ret (Some AssertNMaxSize, Some b, None, None)
          | ModOk x1 =>
              do c <- copy x1 ;                               (* [comment removed for export] *)
              destroy x1 ;;                                   (* [comment removed for export] *)
              do x2 <- copy b ;                               (* [comment removed for export] *)
              do m2 <- mod_assign x2 a ;                      (* [comment removed for export] *)
              match m2 with
              | ModZero =>
                  destroy x2 ;; destroy c ;; destroy b ;; destroy a ;; emit ECatch ;;
                  ret (Some ZeroDivide, Some b, Some c, None)
              | ModAssert xc =>                                (* [comment removed for export] *)
                  destroy xc ;; destroy c ;; destroy b ;; destroy a ;; emit ECatch ;;
                  ret (Some AssertNMaxSize, Some b, Some c, None)
              | ModOk x3 =>
                  do d <- copy x3 ;                           (* [comment removed for export] *)
                  destroy x3 ;;                               (* [comment removed for export] *)
                  destroy d ;; destroy c ;; destroy b ;; destroy a ;;   (* [comment removed for export] *)
                  ret (None, Some b, Some c, Some d)
              end
          end
      end
    end
  else ret (None, None, None, None).

Definition harness (p : list Z) : M (option exn * option sto * option sto * option sto) :=
  let n := length p in
  do sb <- (if (sso_max <? n)%nat then do blk <- alloc (str_alloc_bytes n) SiteString ; ret (Some blk)
            else ret None) ;                                  (* [comment removed for export] *)
  do r <- harness_body p ;
  match sb with
  | Some blk => emit (EFree blk (str_alloc_bytes n)) ;; ret r    (* [comment removed for export] *)
  | None => ret r
  end.

Definition run_payload (p : list Z) : outcome :=
  let '(r, s) := harness p st_init in
  let '(ex, b, c, d) := r in
  Outcome (rev (st_evs s)) ex b c d.

(* [comment removed for export] *)
Definition payload_events (p : list Z) : list event := o_events (run_payload p).

(* [comment removed for export] *)
Example ev_123 : payload_events [49;50;51] = [EAlloc 0 64 SiteReserve; EFree 0 64].
Proof. vm_compute. reflexivity. Qed.

Example ev_empty : payload_events [] = [EAlloc 0 64 SiteReserve; EFree 0 64; EThrow SystemError22; ECatch].
Proof. vm_compute. reflexivity. Qed.

Example ev_zero : payload_events [48] = [EAlloc 0 64 SiteReserve; EFree 0 64; EThrow ZeroDivide; ECatch].
Proof. vm_compute. reflexivity. Qed.
