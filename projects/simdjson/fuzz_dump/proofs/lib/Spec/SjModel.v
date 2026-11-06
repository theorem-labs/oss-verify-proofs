(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require SjS1Out SjStage1 SjStage1Out SjAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

Definition roundup64 (x : Z) : Z := (x + 63) / 64 * 64.
Definition sj_cap (len : Z) : Z := Z.max len 32.
Definition SJ_SBUF (len : Z) : Z := roundup64 (5 * (sj_cap len / 3) + 64).
Definition SJ_TAPE (len : Z) : Z := 8 * roundup64 (sj_cap len + 3).
Definition SJ_IMPL : Z := 96.
Definition SJ_IDX (len : Z) : Z := 4 * (roundup64 (sj_cap len) + 9).
Definition SJ_OC : Z := 8192.
Definition SJ_IA : Z := 1024.
Definition SJ_COPY (len : Z) : Z := len + 64.
Definition SJ_PADMAX : Z := 1048512.

Definition sj_root_copy (d : list Z) : option Z :=
  let bs := SjAlloc.strip_bom d in
  SjAlloc.root_copy bs (SjStage1.stage1_code bs) (SjStage1.stage1_idx0 bs).

Definition rc_ok (len : Z) (rc : option Z) : Prop :=
  match rc with None => True | Some c => 64 <= c <= len + 64 end.

Lemma sj_root_copy_ok : forall d, rc_ok (zlength d) (sj_root_copy d).
Proof.
  intros d. unfold sj_root_copy, SjAlloc.root_copy. set (bs := SjAlloc.strip_bom d).
  destruct ((SjStage1.stage1_code bs =? 0) && SjAlloc.is_numstart_b (SjS1Out.B bs (SjStage1.stage1_idx0 bs))) eqn:E; [| exact I].
  apply andb_prop in E. destruct E as [E _]. apply Z.eqb_eq in E.
  unfold SjStage1.stage1_code in E. unfold SjStage1.stage1_idx0.
  destruct (SjStage1.stage1 bs) as [c idxs] eqn:ES. cbn [fst snd] in *. subst c.
  pose proof (SjStage1Out.stage1_S1OUT bs idxs ES) as SO.
  pose proof (SjS1Out.s1_nonempty _ _ SO) as NE. pose proof (SjS1Out.s1_range _ _ SO) as RG.
  destruct idxs as [|i0 rest]; [contradiction NE; reflexivity|]. cbn [hd].
  inversion RG as [|x l Hi0 _]; subst.
  pose proof (SjAlloc.blen_strip_bom d) as HB. fold bs in HB.
  cbn [rc_ok]. unfold SjS1Out.blen, zlength in *. lia.
Qed.

Lemma roundup64_ge : forall x, x <= roundup64 x.
Proof. intros x. unfold roundup64. pose proof (Z.div_mod (x + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 63) 64 ltac:(lia)). lia. Qed.
Lemma roundup64_lt : forall x, roundup64 x < x + 64.
Proof. intros x. unfold roundup64. pose proof (Z.div_mod (x + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 63) 64 ltac:(lia)). lia. Qed.

Lemma sj_sizes_bound : forall len, 0 <= len < 2^26 ->
  0 < SJ_SBUF len <= 111848256 /\ 0 < SJ_TAPE len <= 2^29 + 1024 /\ 0 < SJ_IDX len <= 2^28 + 512 /\ 0 < SJ_COPY len < 2^26 + 64.
Proof.
  intros len H. unfold SJ_SBUF, SJ_TAPE, SJ_IDX, SJ_COPY, sj_cap.
  pose proof (roundup64_ge (5 * (Z.max len 32 / 3) + 64)). pose proof (roundup64_lt (5 * (Z.max len 32 / 3) + 64)).
  pose proof (roundup64_ge (Z.max len 32 + 3)). pose proof (roundup64_lt (Z.max len 32 + 3)).
  pose proof (roundup64_ge (Z.max len 32)). pose proof (roundup64_lt (Z.max len 32)).
  assert (0 <= Z.max len 32 / 3 <= 22369621) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  change (2^26) with 67108864 in *. change (2^29) with 536870912. change (2^28) with 268435456. lia.
Qed.

Inductive tevent : Type :=
| TMalloc (n : Z) (r : option nat)
| TFree (p : option nat)
| TStderr (bytes : list Z)
| TStdout (bytes : list Z)
| TMsgStore (bytes : list Z)
| TReturn (rc : Z)
| TUnreachable.

Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;
  lib_malloc : Z -> M (option ptr);
  lib_free : option ptr -> M unit;
  out_stderr : list Z -> M unit;
  out_stdout : list Z -> M unit;
  msg_store : list Z -> M unit;
  cho : M Z
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.
Arguments cho {M ptr}.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition newnt (n : Z) : M ptr :=
  r <- lib_malloc ops n ;;
  match r with Some p => ret ops p | None => unreachable ops end.

Definition del (p : ptr) : M unit := lib_free ops (Some p).

Definition copy_phase (len : Z) (rc : option Z) : M unit :=
  if len <=? SJ_PADMAX then
    cp <- newnt (SJ_COPY len) ;;
    (match rc with
     | Some c => r <- newnt c ;; del r
     | None => ret ops tt
     end) ;;;
    del cp
  else ret ops tt.

Definition fuzz_one_with (rc : option Z) : M Z :=
  let len := zlength d in
  sb <- newnt (SJ_SBUF len) ;;
  tp <- newnt (SJ_TAPE len) ;;
  im <- newnt SJ_IMPL ;;
  ix <- newnt (SJ_IDX len) ;;
  oc <- newnt SJ_OC ;;
  ia <- newnt SJ_IA ;;
  copy_phase len rc ;;;
  del sb ;;; del tp ;;; del ia ;;; del oc ;;; del ix ;;; del im ;;;
  ret ops 0.

Definition fuzz_one : M Z := fuzz_one_with (sj_root_copy d).

Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_calls n' rc'
  end.

Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Module SjRun.

Inductive ttree (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TEv (e : tevent) (k : ttree A)
| TMallocQ (n : Z) (k : option nat -> ttree A)
| TChoQ (k : Z -> ttree A).
Arguments TRet {A}.
Arguments TUnr {A}.
Arguments TEv {A}.
Arguments TMallocQ {A}.
Arguments TChoQ {A}.

Fixpoint tbind {A B} (m : ttree A) (f : A -> ttree B) : ttree B :=
  match m with
  | TRet a => f a
  | TUnr => TUnr
  | TEv e k => TEv e (tbind k f)
  | TMallocQ n k => TMallocQ n (fun r => tbind (k r) f)
  | TChoQ k => TChoQ (fun z => tbind (k z) f)
  end.

Definition tree_ops : target_ops ttree nat :=
  mkOps (fun A (a : A) => TRet a)
        (fun A B m f => tbind m f)
        (fun A => TUnr)
        (fun n => TMallocQ n (fun r => TRet r))
        (fun p => TEv (TFree p) (TRet tt))
        (fun bs => TEv (TStderr bs) (TRet tt))
        (fun bs => TEv (TStdout bs) (TRet tt))
        (fun bs => TEv (TMsgStore bs) (TRet tt))
        (TChoQ (fun z => TRet z)).

Definition target_tree (cfg payload : list Z) : ttree Z :=
  target_run tree_ops payload cfg.

Fixpoint run_tree_c {A} (t : ttree A) (oracle : list bool) (coracle : list Z) (next : nat) (acc : list tevent)
  : list tevent * option A :=
  match t with
  | TRet a => (rev acc, Some a)
  | TUnr => (rev (TUnreachable :: acc), None)
  | TEv e k => run_tree_c k oracle coracle next (e :: acc)
  | TMallocQ n k =>
      let '(ok, oracle') := match oracle with
                            | [] => (true, [])
                            | b :: o' => (b, o')
                            end in
      let r := if ok then Some next else None in
      run_tree_c (k r) oracle' coracle (S next) (TMalloc n r :: acc)
  | TChoQ k =>
      let '(z, coracle') := match coracle with
                            | [] => (0, [])
                            | z :: c' => (z, c')
                            end in
      run_tree_c (k z) oracle coracle' next acc
  end.
Definition run_tree {A} (t : ttree A) (oracle : list bool) (next : nat) (acc : list tevent) : list tevent * option A :=
  run_tree_c t oracle [] next acc.

Definition target_events (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := run_tree (target_tree cfg payload) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End SjRun.

Module SjModelTests.
Import SjRun.

Example ex_len7_one_call :
  target_events [0] [91; 49; 44; 50; 44; 51; 93] []
  = [TMalloc 7 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 71 (Some 7%nat);
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_empty :
  target_events [] [] []
  = [TMalloc 128 (Some 0%nat); TMalloc 512 (Some 1%nat); TMalloc 96 (Some 2%nat); TMalloc 292 (Some 3%nat);
     TMalloc 8192 (Some 4%nat); TMalloc 1024 (Some 5%nat); TMalloc 64 (Some 6%nat);
     TFree (Some 6%nat);
     TFree (Some 0%nat); TFree (Some 1%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat); TFree (Some 2%nat);
     TStdout [48; 10]; TFree None; TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_root_number :
  target_events [0] [32; 49; 50] []
  = [TMalloc 3 (Some 0%nat);
     TMalloc 128 (Some 1%nat); TMalloc 512 (Some 2%nat); TMalloc 96 (Some 3%nat); TMalloc 292 (Some 4%nat);
     TMalloc 8192 (Some 5%nat); TMalloc 1024 (Some 6%nat); TMalloc 67 (Some 7%nat);
     TMalloc 66 (Some 8%nat); TFree (Some 8%nat);
     TFree (Some 7%nat);
     TFree (Some 1%nat); TFree (Some 2%nat); TFree (Some 6%nat); TFree (Some 5%nat); TFree (Some 4%nat); TFree (Some 3%nat);
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof. vm_compute. reflexivity. Qed.

Example ex_client_null :
  target_events [0] [55] [true; true; false]
  = [TMalloc 1 (Some 0%nat); TMalloc 128 (Some 1%nat); TMalloc 512 None; TUnreachable].
Proof. vm_compute. reflexivity. Qed.

Example ex_copy_fail :
  target_events [3] [65] [false] = [TMalloc 1 None; TReturn 2].
Proof. vm_compute. reflexivity. Qed.

End SjModelTests.
