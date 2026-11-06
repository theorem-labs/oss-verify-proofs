(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

(* [comment removed for export] *)
Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;        (* [comment removed for export] *)
  lib_malloc : Z -> M (option ptr);          (* [comment removed for export] *)
  lib_free : option ptr -> M unit;           (* [comment removed for export] *)
  choose : (cho -> Prop) -> M cho;           (* [comment removed for export] *)
  out_stderr : list Z -> M unit;             (* [comment removed for export] *)
  out_stdout : list Z -> M unit;             (* [comment removed for export] *)
  msg_store : list Z -> M unit               (* [comment removed for export] *)
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments choose {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.

(* [comment removed for export] *)
Definition TIER_A_MAX : Z := 236.            (* [comment removed for export] *)
Definition CAP_A : Z := 8184.            (* [comment removed for export] *)
Definition CAP_B : Z := 60.
Definition BIG_ROOM : Z := 600000000.
Definition SZ_MAX : Z := 2^31.
Definition INIT_FUEL : nat := (128 * 128)%nat.
Definition CALL_FUEL (plen : Z) : nat := Z.to_nat (64 + 8 * plen).

Section ClientList.
Context {ptr : Type}.
Definition clist : Type := list (ptr * Z).
Definition cntA (L : clist) : Z := Z.of_nat (length (filter (fun xb => snd xb <=? TIER_A_MAX) L)).
Definition cntB (L : clist) : Z := Z.of_nat (length (filter (fun xb => TIER_A_MAX <? snd xb) L)).
Definition bigsum (L : clist) : Z := fold_right (fun xb acc => (if TIER_A_MAX <? snd xb then snd xb + 8192 else 0) + acc) 0 L.
Fixpoint cremove (i : nat) (L : clist) : clist :=
  match L, i with
  | [], _ => []
  | _ :: L', O => L'
  | x :: L', S i' => x :: cremove i' L'
  end.
Definition cvalid (L : clist) (a : cho) : Prop :=
  match a with
  | Cho 0 _ _ => True
  | Cho 1 n _ => 0 <= n < SZ_MAX
                 /\ (n <= TIER_A_MAX -> cntA L < CAP_A)
                 /\ (TIER_A_MAX < n -> cntB L < CAP_B /\ bigsum L + n + 8192 <= BIG_ROOM)
  | Cho 2 i _ => 0 <= i < Z.of_nat (length L)
  | _ => False
  end.
End ClientList.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.          (* [comment removed for export] *)

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 100, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 100, right associativity).

(* [comment removed for export] *)
Fixpoint client_any (fuel : nat) (L : @clist ptr) : M (@clist ptr) :=
  match fuel with
  | O => ret ops L
  | S f =>
      a <- choose ops (cvalid L) ;;
      match a with
      | Cho 1 n _ =>
          r <- lib_malloc ops n ;;
          match r with
          | None => unreachable ops                          (* [comment removed for export] *)
          | Some p => client_any f ((p, n) :: L)
          end
      | Cho 2 i _ =>
          match nth_error L (Z.to_nat i) with
          | None => unreachable ops                          (* [comment removed for export] *)
          | Some (p, _) => lib_free ops (Some p) ;;; client_any f (cremove (Z.to_nat i) L)
          end
      | _ => ret ops L                                       (* [comment removed for export] *)
      end
  end.

(* [comment removed for export] *)
Definition fuzz_init : M (@clist ptr) := client_any INIT_FUEL [].
Definition fuzz_one (L : @clist ptr) : M (Z * @clist ptr) :=
  L' <- client_any (CALL_FUEL (zlength d)) L ;; ret ops (0, L').

(* [comment removed for export] *)
Fixpoint run_calls (n : nat) (rc : Z) (L : @clist ptr) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      r <- fuzz_one L ;;
      out_stdout ops (Zdecimal (fst r) ++ [10]) ;;;   (* [comment removed for export] *)
      run_calls n' (fst r) (snd r)
  end.

(* [comment removed for export] *)
Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in       (* [comment removed for export] *)
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  L0 <- fuzz_init ;;                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2                                          (* [comment removed for export] *)
  | Some owned =>
      rc <- run_calls calls 0 L0 ;;
      lib_free ops owned ;;;                                   (* [comment removed for export] *)
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.
